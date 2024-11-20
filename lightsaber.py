#libs foda
from sage.all import*
from Crypto.Hash import SHAKE128, SHA3_512, SHAKE256 #o algoritmo sha3/shake* deve ser utilizado no kyber pois serve como XOF
from dataclasses import dataclass
from Crypto.Random import get_random_bytes
from itertools import chain
def convrt(a,length):str_bits=bin(a)[2:];padding_length=length-len(str_bits);return[int(b)for b in reversed(str_bits)]+[0]*padding_length
@dataclass
class Kyberconfig:nivel_seguranca:int;q:int;n:int;k:int;eta1:int;eta2:int;du:int;dv:int
class Lightsaber:
	Nivelk={128:Kyberconfig(nivel_seguranca=128,q=3329,n=256,k=2,eta1=3,eta2=2,du=10,dv=4)} #KYBER512 nivel de seguranca 1
	def __init__(self,nivel_seguranca):assert nivel_seguranca in self.Nivelk;self.params=self.Nivelk[nivel_seguranca];self.F=GF(self.params.q);self.polynomial_ring=PolynomialRing(self.F,'x');self.nth_root_unity=self.F(17)
	def dftanel(self,a):
		n=len(a)
		if n==1:return a
		else:even=self.dftanel(a[0::2]);odd=self.dftanel(a[1::2]);w=[self.nth_root_unity**(i*(self.params.n//n))for i in range(n)];return[even[i]+w[i]*odd[i]for i in range(n//2)]+[even[i]-w[i]*odd[i]for i in range(n//2)]
	def dftanel_i(self,a_hat):
		n=len(a_hat)
		if n==1:return a_hat
		else:even=self.dftanel_i(a_hat[0::2]);odd=self.dftanel_i(a_hat[1::2]);w=[self.nth_root_unity**(-i*(self.params.n//n))for i in range(n)];return[(even[i]+w[i]*odd[i])/2 for i in range(n//2)]+[(even[i]-w[i]*odd[i])/2 for i in range(n//2)]
	def ger_anelpolinomial(self,rho,j,i):
		seed_bytes=rho+int(j).to_bytes(1,byteorder='big')+int(i).to_bytes(1,byteorder='big')
		xof=SHAKE128.new(seed_bytes);hat_a=[None]*self.params.n;k=0
		while k<self.params.n:
			b0,b1,b2=[int.from_bytes(xof.read(1),byteorder='big')for _ in range(3)];d1=b0+256*(b1%16);d2=b1//16+16*b2
			if d1<self.params.q:hat_a[k]=d1;k+=1
			if d2<self.params.q and k<self.params.n:hat_a[k]=d2;k+=1
		return vector(self.F,hat_a)
	def fourier_an_s(self,rho):
		dftanel_A=[[None]*self.params.k for _ in range(self.params.k)]
		for i in range(self.params.k):
			for j in range(self.params.k):dftanel_A[i][j]=self.ger_anelpolinomial(rho,j,i)
		return dftanel_A
	def fourier_tn_s(self,rho):
		dftanel_A=[[None]*self.params.k for _ in range(self.params.k)]
		for i in range(self.params.k):
			for j in range(self.params.k):dftanel_A[i][j]=self.ger_anelpolinomial(rho,i,j)
		return dftanel_A
	def cnvrtb_pb(self,byte_array):
		bits=[]
		for b in byte_array:bits+=convrt(b,8)
		return bits
	def distrib_binomial(self,eta,seed):
		bytes_array=SHAKE256.new(seed).read(64*eta);bits=self.cnvrtb_pb(bytes_array);f=[]
		for i in range(self.params.n):index=2*i*eta;a=sum(bits[index:index+eta]);b=sum(bits[index+eta:index+2*eta]);f.append(a-b)
		return f
	def distrib_binomial2(self,eta,seed,base_quantidade):seed_quantidade_bytes=seed+int(base_quantidade).to_bytes(1,byteorder='big');poly_coeffs=self.distrib_binomial(eta,seed_quantidade_bytes);return vector(self.F,poly_coeffs),1
	def db3(self,eta,seed,base_quantidade):
		v=[]
		for i in range(self.params.k):seed_quantidade_bytes=seed+int(base_quantidade+i).to_bytes(1,byteorder='big');poly_coeffs=self.distrib_binomial(eta,seed_quantidade_bytes);v.append(vector(self.F,poly_coeffs))
		return v,self.params.k
	def sig(self,sigma):
		s=[];quantidade=0
		for i in range(self.params.k):poly_coeffs=self.distrib_binomial(self.params.eta1,sigma+int(quantidade).to_bytes(1));s.append(vector(self.F,poly_coeffs));quantidade+=1
		e=[]
		for i in range(self.params.k):poly_coeffs=self.distrib_binomial(self.params.eta1,sigma+int(quantidade).to_bytes(1));e.append(vector(self.F,poly_coeffs));quantidade+=1
		return s,e
	def fourier_prod(self,pol,dftanel_poly2):return vector(self.F,[c1*c2 for(c1,c2)in zip(pol,dftanel_poly2)])
	def fourier_vetor(self,fouri1,fouri2):
		dftanel_produtoo=zero_vector(self.F,self.params.n)
		for i in range(self.params.k):dftanel_produtoo+=self.fourier_prod(fouri1[i],fouri2[i])
		return dftanel_produtoo
	def fourier_matriz_polinomial(self,dftanel_matrix,fouri):
		dftanel_result=[[None]*self.params.k for _ in range(self.params.k)]
		for i in range(self.params.k):dftanel_result[i]=self.fourier_vetor(dftanel_matrix[i],fouri)
		return dftanel_result
	def srerro(self,vetorz,vetorx):
		srerro=[None]*self.params.k
		for i in range(self.params.k):srerro[i]=vector(self.F,vetorz[i])+vector(self.F,vetorx[i])
		return srerro
	def gerapubpriv(self):d=get_random_bytes(32);hash_g_of_d=SHA3_512.new(d).digest();rho,sigma=hash_g_of_d[:16],hash_g_of_d[16:];dftanel_A=self.fourier_an_s(rho);quantidade=0;s,quantidade=self.db3(self.params.eta1,sigma,quantidade);e,quantidade=self.db3(self.params.eta1,sigma,quantidade);dftanel_s=[self.dftanel(s_i)for s_i in s];dftanel_e=[self.dftanel(e_i)for e_i in e];dftanel_t=self.srerro(self.fourier_matriz_polinomial(dftanel_A,dftanel_s),dftanel_e);return(dftanel_t,rho),dftanel_s
	def fouri(self,vector):return[self.dftanel(v)for v in vector]
	def dftanel_i_vetor(self,vector):return[self.dftanel_i(v)for v in vector]
	def comp(self,coeficiente,d):return[self.comp_coeficiente(c,d)for c in coeficiente]
	def decomp(self,coeficiente,d):return vector(self.F,[self.decomp_coeficiente(c,d)for c in coeficiente])
	def comp_coeficiente(self,x,d):return mod(round(2**d/self.params.q*int(x)),2**d)
	def decomp_coeficiente(self,x,d):return round(self.params.q/2**d*int(x))
	def encapsula(self,pk,txt,rnd):dftanel_t,rho=pk;dftanel_A_transpose=self.fourier_tn_s(rho);quantidade=0;r,quantidade=self.db3(self.params.eta1,rnd,quantidade);e1,quantidade=self.db3(self.params.eta1,rnd,quantidade);e2,quantidade=self.distrib_binomial2(self.params.eta1,rnd,quantidade);dftanel_r=self.fouri(r);u=self.dftanel_i_vetor(self.fourier_matriz_polinomial(dftanel_A_transpose,dftanel_r)+e1);encoded_txt=self.decomp(txt,1);v=vector(self.F,encoded_txt)+vector(self.F,self.dftanel_i(self.fourier_vetor(dftanel_t,dftanel_r)))+vector(self.F,e2);u_comped=[self.comp(u_i,self.params.du)for u_i in u];v_comped=self.comp(v,self.params.dv);return u_comped,v_comped
	def desencapsula(self,sk,encapsuladoo):dftanel_s=sk;u_comped,v_comped=encapsuladoo;u=[self.decomp(u_i,self.params.du)for u_i in u_comped];v=self.decomp(v_comped,self.params.dv);dftanel_u=self.fouri(u);noisy_txt=v-vector(self.F,self.dftanel_i(self.fourier_vetor(dftanel_s,dftanel_u)));return self.comp(noisy_txt,1)

lightsaber=Lightsaber(128) #AES-128 / KYBER-512
pk,sk=lightsaber.gerapubpriv()
txt=[1,3,3,7] #mensagem
if len(txt)!=lightsaber.params.n:txt=txt+[0]*(lightsaber.params.n-len(txt)) #reduz a mensagem se for maior que o suportado
encapsuladoo=lightsaber.encapsula(pk,vector(lightsaber.F,txt),b'') #encapsula
print('\n\033[1mencapsulado:\033[0m',encapsuladoo)
txtd=lightsaber.desencapsula(sk,encapsuladoo) #desencapsulacao
print('\n\033[1mdesencapsulado:\033[0m',txtd)

// Weird Odd Search by Wenjie Fang (aka fwjmath) from Team China
// Licensed under GPLv3
// Contact: fwjmath -replace.these.words.by.at- gmail.com
// Only applicable to numbers strictly less than 2^63, prefereably less than 10^18 to be sure.
// Only works on 64bit machine, where unsigned long int has 64 bits.

#include <stdio.h>
#include <algorithm>
#include "gmp.h"
#include "gmpxx.h"
#include "trn/trn.h"

#define PRIME_COUNT 2064
#define BATCH_LEN_1 32
#define INITIAL_SEG 16
#define BRENT_PERIOD 16

unsigned int primes[PRIME_COUNT];
mpz_class batch1[(PRIME_COUNT - INITIAL_SEG)/BATCH_LEN_1];

unsigned long long factor[64]; // We are under 2^64
unsigned int multiplicity[64];
unsigned int factor_cnt;

unsigned long int n, cofactor, factored;
mpz_class presum;

// General temporary variables. Do not use in recursive calls.
mpz_class gtmp, gtmp1, gtmp2;
unsigned long int tmp, tmp1, tmp2, tmp3, tmp4;

// Variables for Pollard Rho Brent variant
mpz_class brent_x, brent_y, brent_batch, brent_ssx, brent_ssy;
unsigned int brent_cnt, brent_aim, brent_iter;
unsigned long long brent_gcd;

// Prime factoring barrier: after trial factoring, unfactored numbers under this barrier are prime
unsigned long long prime_barrier;

// Temporary variable solely used to record multiplicity of prime factors
int p;

// Congruence array, used to trial factor small primes
int congruence[INITIAL_SEG];

// Divisors array
#define DIVISOR_BOUND 1048576
unsigned long long divisors[DIVISOR_BOUND];
unsigned int divisor_cnt;

// Checksum mechanism
unsigned long int checksum;

FILE* fio;

__inline void readTable(){
	fio = fopen("primes.txt","r");
	int i;
	for(i = 0; i < PRIME_COUNT; i++) fscanf(fio, "%d", &(primes[i]));
	fclose(fio);
	for(i = 0; i < (PRIME_COUNT - INITIAL_SEG) / BATCH_LEN_1; i++){
		batch1[i]=1;
		for(int j = 0; j < BATCH_LEN_1; j++)
			batch1[i] *= primes[INITIAL_SEG + BATCH_LEN_1 * i + j];
	}
	prime_barrier=primes[PRIME_COUNT-1];
	prime_barrier*=prime_barrier;
	return;
}

__inline void factor_init(){
	cofactor=n;
	factor_cnt=0;
	presum=1;
	factored=2;
	return;
}

// In congruence[i] we store -n mod primes[i]
__inline void congruence_init(){
	for(int i=0;i<INITIAL_SEG;i++){
		congruence[i]=n%primes[i];
		if(congruence[i]!=0) congruence[i]=primes[i]-congruence[i];
	}
	return;
}

__inline void trial_factor_3(){
	p=0;
	tmp=1;
	tmp1=1;
	do{
		cofactor/=3;
		factored*=3;
		tmp*=3;
		tmp1+=tmp;
		p++;
	}while((cofactor%3)==0);
	factor[factor_cnt]=3;
	multiplicity[factor_cnt]=p;
	factor_cnt++;
	presum*=tmp1;
	return;
}

__inline void trial_factor_5(){
	p=0;
	tmp=1;
	tmp1=1;
	do{
		cofactor/=5;
		factored*=5;
		tmp*=5;
		tmp1+=tmp;
		p++;
	}while((cofactor%5)==0);
	factor[factor_cnt]=5;
	multiplicity[factor_cnt]=p;
	factor_cnt++;
	presum*=tmp1;
	return;
}

// Contract: every number trial-factored is divisible by either 3 or 5 
// OEIS A047802, abundant number filtering
bool trial_factor_small(){
	
	// We want to search for the smallest odd weird number wn
	// If wn has a proper factor fc that is abundant, either fc is semi-perfect or weird
	// fc cannot be semi-perfect, or else wn will also be semi-perfect but not weird
	// fc cannot be weird, or wn will not be the smallest weird number
	// Therefore, wn can have no proper factor that is abundant
	if(cofactor==1) return true;
	if(presum>=factored) return false; 

	for(int i=0;i<INITIAL_SEG;i++){
		if(congruence[i]==0){
			p=0;
			tmp=1;
			tmp1=1;
			do{
				cofactor/=primes[i];
				tmp*=primes[i];
				tmp1+=tmp;
				p++;
			}while((cofactor%primes[i])==0);
			factor[factor_cnt]=primes[i];
			multiplicity[factor_cnt]=p;
			factor_cnt++;
			factored*=tmp;
			presum*=tmp1; 
			if(cofactor==1) return true;
			if(presum>=factored) return false;
		}
	}
	return true;
}


bool trial_factor_batch(){
	unsigned int p;
	if(cofactor==1) return true;
	for(int i=0; i<(PRIME_COUNT - INITIAL_SEG) / BATCH_LEN_1; i++){
		
		// Big formula sieve
		tmp1=primes[INITIAL_SEG - 1 + (i) * BATCH_LEN_1];
		if((cofactor*tmp1)/tmp1==cofactor){
			tmp=tmp1;
			tmp3=tmp1-1;
			tmp4=tmp3;
			p=1;
			while(tmp<cofactor){ p++; tmp*=tmp1; tmp4*=tmp3; }
			gtmp2=tmp4;
			gtmp2+=gtmp2;
			gtmp1=presum*cofactor;
			gtmp1*=tmp;
			gtmp2*=n;
			if(gtmp1<=gtmp2) return false;
		}else{
			gtmp=tmp1;
			p=1;
			while(gtmp<cofactor){ p++; gtmp*=tmp1; }
			gtmp2=tmp1-1;
			mpz_pow_ui(gtmp2.get_mpz_t(),gtmp2.get_mpz_t(),p);
			gtmp1=presum*cofactor;
			gtmp1*=gtmp;
			gtmp2*=n;
			gtmp2+=gtmp2;
			if(gtmp1<=gtmp2) return false;
		}
		// End of sieve
		
		tmp=mpz_gcd_ui(NULL, batch1[i].get_mpz_t(), cofactor);
		if(tmp!=1){
			tmp1=primes[INITIAL_SEG - 1 + (i+1) * BATCH_LEN_1];
			
			// Case one prime: the only factor
			if(tmp<=tmp1){
				p=0;
				tmp2=1;
				tmp3=1;
				do{
					cofactor/=tmp;
					tmp2*=tmp;
					tmp3+=tmp2;
					p++;
				}while((cofactor%tmp)==0);
				factor[factor_cnt]=tmp;
				multiplicity[factor_cnt]=p;
				factor_cnt++;
				presum*=tmp3;
				continue;
			}
			
			// Case two primes: using Fermat's method
			tmp1*=tmp1;
			if(tmp<=tmp1){
				gtmp=tmp-1;
				mpz_sqrt(gtmp.get_mpz_t(), gtmp.get_mpz_t());
				gtmp++;
				if((tmp&3)==1){
					if(mpz_even_p(gtmp.get_mpz_t())) gtmp++;
				}else{
					if(mpz_odd_p(gtmp.get_mpz_t())) gtmp++;
				}
				tmp2=mpz_get_ui(gtmp.get_mpz_t());
				gtmp*=gtmp;
				gtmp-=tmp;
				while(mpz_perfect_square_p(gtmp.get_mpz_t())==0){
					gtmp+=((tmp2+1)<<2);
					tmp2+=2;
				}
				mpz_sqrt(gtmp.get_mpz_t(),gtmp.get_mpz_t());
				tmp1=mpz_get_ui(gtmp.get_mpz_t());
				
				tmp=tmp2-tmp1;
				p=0;
				tmp3=1;
				tmp4=1;
				do{
					cofactor/=tmp;
					tmp3*=tmp;
					tmp4+=tmp3;
					p++;
				}while((cofactor%tmp)==0);
				factor[factor_cnt]=tmp;
				multiplicity[factor_cnt]=p;
				factor_cnt++;
				presum*=tmp4;
				
				if(tmp1==0) continue;
				tmp=tmp2+tmp1;
				p=0;
				tmp3=1;
				tmp4=1;
				do{
					cofactor/=tmp;
					tmp3*=tmp;
					tmp4+=tmp3;
					p++;
				}while((cofactor%tmp)==0);
				factor[factor_cnt]=tmp;
				multiplicity[factor_cnt]=p;
				factor_cnt++;
				presum*=tmp4;
				
				continue;
			}
			
			// Case unlucky: do it for all primes
			
			tmp1=primes[INITIAL_SEG - 1 + (i+1) * BATCH_LEN_1];
			for(int j=INITIAL_SEG+i*BATCH_LEN_1; j<INITIAL_SEG+(i+1)*BATCH_LEN_1; j++){
				if((tmp%primes[j])==0){
					p=0;
					tmp3=1;
					tmp4=1;
					do{
						cofactor/=primes[j];
						tmp3*=primes[j];
						tmp4+=tmp3;
						p++;
					}while((cofactor%primes[j])==0);
					factor[factor_cnt]=primes[j];
					multiplicity[factor_cnt]=p;
					factor_cnt++;
					presum*=tmp4;
					tmp/=primes[j];
					if((tmp<=tmp1)&&(tmp>1)){
						p=0;
						tmp3=1;
						tmp4=1;
						do{
							cofactor/=tmp;
							tmp3*=tmp;
							tmp4+=tmp3;
							p++;
						}while((cofactor%tmp)==0);
						factor[factor_cnt]=tmp;
						multiplicity[factor_cnt]=p;
						factor_cnt++;
						presum*=tmp4;
						break;
					}
				}
			}
		}
		if(cofactor==1) return true;
		factored=n/cofactor;
		factored+=factored;
		if(presum>=factored) return false;
		
	}
	
	// Big formula sieve
	tmp1=primes[INITIAL_SEG - 1 + ((PRIME_COUNT - INITIAL_SEG) / BATCH_LEN_1) * BATCH_LEN_1];
	if((cofactor*tmp1)/tmp1==cofactor){
		tmp=tmp1;
		tmp3=tmp1-1;
		tmp4=tmp3;
		p=1;
		while(tmp<cofactor){ p++; tmp*=tmp1; tmp4*=tmp3; }
		gtmp2=tmp4;
		gtmp2+=gtmp2;
		gtmp1=presum*cofactor;
		gtmp1*=tmp;
		gtmp2*=n;
		if(gtmp1<=gtmp2) return false;
	}else{
		gtmp=tmp1;
		p=1;
		while(gtmp<cofactor){ p++; gtmp*=tmp1; }
		gtmp2=tmp1-1;
		mpz_pow_ui(gtmp2.get_mpz_t(),gtmp2.get_mpz_t(),p);
		gtmp1=presum*cofactor;
		gtmp1*=gtmp;
		gtmp2*=n;
		gtmp2+=gtmp2;
		if(gtmp1<=gtmp2) return false;
	}
	// End of sieve
	
	return true;
}

unsigned long long brent(unsigned int c, unsigned long long nn){
	brent_x=2;
	brent_y=2;
	brent_gcd=1;
	brent_cnt=0;
	brent_iter=1;
	brent_aim=2;
	
	while((brent_gcd==1)&&(brent_aim<BRENT_PERIOD)){
		brent_x*=brent_x;
		brent_x+=c;
		mpz_mod_ui(brent_x.get_mpz_t(), brent_x.get_mpz_t(), nn);
		
		brent_batch = brent_x-brent_y;
		brent_gcd = mpz_gcd_ui(NULL,brent_batch.get_mpz_t(),nn);
		
		brent_iter++;
		if(brent_iter==brent_aim){
			brent_aim<<=1;
			brent_y=brent_x;
		}
	}
	
	brent_batch=1;
	brent_ssx=brent_x;
	brent_ssy=brent_y;
	
	while(brent_gcd==1){
		brent_x*=brent_x;
		brent_x+=c;
		mpz_mod_ui(brent_x.get_mpz_t(), brent_x.get_mpz_t(), nn);
		gtmp=brent_x-brent_y;
		brent_batch*=gtmp;
		
		brent_iter++;
		if(brent_iter==brent_aim){
			brent_aim<<=1;
			brent_y=brent_x;
		}
		
		brent_cnt++;
		if(brent_cnt==BRENT_PERIOD){
			brent_gcd = mpz_gcd_ui(NULL,brent_batch.get_mpz_t(),nn);
			if(brent_gcd!=1) break;
			brent_batch=1;
			brent_cnt=0;
			brent_ssx=brent_x;
			brent_ssy=brent_y;
		}
	}
	
	if(brent_gcd!=nn) return brent_gcd;

	// Recycle
	
	brent_x=brent_ssx;
	brent_y=brent_ssy;
	brent_batch=brent_x-brent_y;
	brent_gcd = mpz_gcd_ui(NULL,brent_batch.get_mpz_t(),nn);
	
	if((brent_gcd!=1)&&(brent_gcd!=nn)) return brent_gcd;
	
	for(brent_cnt=0;brent_cnt<=BRENT_PERIOD;brent_cnt++){
		brent_x*=brent_x;
		brent_x+=c;
		mpz_mod_ui(brent_x.get_mpz_t(), brent_x.get_mpz_t(), nn);
		
		brent_batch = brent_x-brent_y;
		brent_gcd = mpz_gcd_ui(NULL,brent_batch.get_mpz_t(),nn);
		if(brent_gcd!=1) break;
	}
	
	if((brent_gcd!=1)&&(brent_gcd!=nn)) return brent_gcd;
	
	return brent(c+1, nn);
}

// For debug
void print_factors(){
	//char c;
	printf("%lu = ", n);
	printf("%llu ^ %d", factor[0], multiplicity[0]);
	for(int i=1;i<factor_cnt;i++) printf(" * %llu ^ %d", factor[i], multiplicity[i]);
	printf("\n");
	/*
	scanf("%c",&c);
	scanf("%c",&c);
	*/
	return;
}

// When we return true, the number should always be abundant.
bool full_factor(){
	if(!trial_factor_small()) return false;
	if(!trial_factor_batch()) { return false; }
	if(cofactor==1){
		if(presum<(n<<1)) return false;
		return true;
	}
	if(cofactor<prime_barrier){
		factor[factor_cnt]=cofactor;
		multiplicity[factor_cnt]=1;
		factor_cnt++;
		presum*=cofactor+1;
		if(presum<(n<<1)) return false;
		cofactor=1;
		return true;
	}
	// We have a rather large factor, but the number is still probably abundant, and after all those sieves.
	// What a miracle!
	unsigned int c=1;
	while(cofactor!=1){
		gtmp=cofactor;
		if(iBPSW(gtmp.get_mpz_t())!=0){
			factor[factor_cnt]=cofactor;
			multiplicity[factor_cnt]=1;
			factor_cnt++;
			presum*=cofactor+1;
			if(presum<(n<<1)) return false;
			cofactor=1;
			return true;
		}
		// brent(unsigned int, unsigned long long) never uses tmp2!
		tmp2=brent(c,cofactor);
		gtmp=tmp2;
		while((tmp2>prime_barrier)&&(iBPSW(gtmp.get_mpz_t())==0)){
			c++;
			tmp2=brent(c, tmp2);
		}
		c++;
		p=0;
		do{
			cofactor/=tmp2;
			p++;
		}while((cofactor%tmp2)==0);
		factor[factor_cnt]=tmp2;
		multiplicity[factor_cnt]=p;
		factor_cnt++;
		gtmp=tmp2;   // Done before, but to make sure
		mpz_pow_ui(gtmp.get_mpz_t(), gtmp.get_mpz_t(), p+1);
		gtmp-=1;
		mpz_divexact_ui(gtmp.get_mpz_t(), gtmp.get_mpz_t(), tmp2-1);
		presum*=gtmp;
		if(cofactor==1) return (presum>(n<<1));
		factored=n/cofactor;
		factored<<=1;
		if(presum>=factored) return false;
	}
	if(presum<(n<<1)) return false;
	return true;
}

bool generate_divisors(unsigned long long aim){
	tmp=1;
	for(int i=0;i<factor_cnt;i++){
		tmp*=multiplicity[i]+1;
	}
	if(tmp>DIVISOR_BOUND){
		// Error handling: too many divisors
		fio=fopen("res.txt","a");
		printf("%lu: too many divisors\n", n);
		fprintf(fio,"%lu: too many divisors\n", n);
		fclose(fio);
		return false;
	}
	divisor_cnt=1;
	divisors[0]=1;
	for(int i=0;i<factor_cnt;i++){
		tmp=divisor_cnt;
		tmp1=factor[i];
		for(int j=0;j<multiplicity[i];j++){
			for(int k=0;k<tmp;k++){
				tmp2=tmp1*divisors[k];
				if(tmp2<=aim){
					divisors[divisor_cnt]=tmp2;
					divisor_cnt++;
				}
			}
			tmp1*=factor[i];
		}
	}
	
	// Remove n
	if(divisors[divisors_cnt-1]==n) divisors_cnt--;
	
	// Sort the divisor list
	std::sort(divisors, divisors+divisor_cnt);
	return true;
}

bool subset_sum(int ptr, unsigned long long aim, unsigned long long avail){
	if(avail<aim) return false;
	if(aim<=1) return true;
	unsigned long long sss2=avail, sss3;
	unsigned int myptr=ptr;
	checksum+=divisors[ptr];
	while(divisors[myptr]>aim){
		sss2-=divisors[myptr];
		myptr--;
	}
	if(sss2<aim) return false;
	if(sss2==aim) return true;
	if(divisors[myptr]==aim) return true;
	if(myptr==0) return false;
	sss3=sss2-aim;
	if(divisors[myptr]==sss3) return true;
	if(sss3>aim){
		if(subset_sum(myptr-1, aim-divisors[myptr], sss2-divisors[myptr])) return true;
		if(subset_sum(myptr-1, aim, sss2-divisors[myptr])) return true;
	}else{
		if(subset_sum(myptr-1, sss3-divisors[myptr], sss2-divisors[myptr])) return true;
		if(subset_sum(myptr-1, sss3, sss2-divisors[myptr])) return true;
	}
	return false;
}

void check_weird(){
	if(full_factor()){
		// Now we are sure that the number is abundant
		//print_factors();
		// Just to be sure
		if(presum<(n<<1)) return;
		gtmp=presum-n;
		gtmp-=n;
		if(!mpz_fits_ulong_p(gtmp.get_mpz_t())){
			// Do some error handling, for example recording the number n
			fio=fopen("res.txt","a");
			printf("Error on %lu!!!\n", n);
			fprintf(fio,"Error on %lu!!!\n", n);
			fclose(fio);
		}
		tmp=mpz_get_ui(gtmp.get_mpz_t());
		//printf("Excess: %lu\n", tmp);
		if(!generate_divisors(tmp)) return;
		tmp=mpz_get_ui(gtmp.get_mpz_t());
		tmp2=0;
		for(int i=0;i<divisor_cnt;i++) tmp2+=divisors[i];
		if(!subset_sum(divisor_cnt-1,tmp,tmp2)){
			// We found a weird number!
			fio=fopen("res.txt","a");
			printf("%lu is WEIRD ODD!!!\n", n);
			fprintf(fio,"%lu is WEIRD ODD!!!\n", n);
			fclose(fio);
		}
	}
	return;
}

__inline void congruence_inc_2(){
	for(int i=0;i<INITIAL_SEG;i++){
		congruence[i]-=2;
		if(congruence[i]<0) congruence[i]+=primes[i];
	}
	return;
}

__inline void congruence_inc_4(){
	for(int i=0;i<INITIAL_SEG;i++){
		congruence[i]-=4;
		if(congruence[i]<0) congruence[i]+=primes[i];
	}
	return;
}

__inline void congruence_inc_6(){
	for(int i=0;i<INITIAL_SEG;i++){
		congruence[i]-=6;
		if(congruence[i]<0) congruence[i]+=primes[i];
	}
	return;
}

int main(){
	
	unsigned long long ub, lb, fake_n, pcnt=0;
	
	fio=fopen("inp.txt","r");
	fscanf(fio,"%llu", &lb);
	fscanf(fio,"%llu", &ub);
	fclose(fio);
	
	//lb=100000000000000001;
	//ub=200000000000000001;
	readTable();
	// Normalizing lower bound and upper bound
	lb-=lb%30;
	ub-=ub%30;
	
	// Checkpoint reading
	fio=fopen("ckpt.txt","r");
	if(fio==NULL){
		n=lb-3;
		checksum=0;
	}else{
		fscanf("%ul %ul", &n, &checksum);
		fclose(fio);
	}
	
	congruence_init();
	for(fake_n=lb; fake_n<ub; fake_n+=30){
		// residue: 27 = -3 -> 3
		n+=6;
		congruence_inc_6();
		factor_init();
		trial_factor_3();
		check_weird();
		// residue: 3 -> 5
		n+=2;
		congruence_inc_2();
		// OEIS A114809: in our range, all abundant number should be divisible by 3 or 7
		if(congruence[0]==0){
			factor_init();
			trial_factor_5();
			check_weird();
		}
		// residue: 5 -> 9
		n+=4;
		congruence_inc_4();
		factor_init();
		trial_factor_3();
		check_weird();
		// residue: 9 -> 15
		n+=6;
		congruence_inc_6();
		factor_init();
		trial_factor_3();
		trial_factor_5();
		check_weird();
		// residue: 15 -> 21
		n+=6;
		congruence_inc_6();
		factor_init();
		trial_factor_3();
		check_weird();
		// residue: 21 -> 25
		n+=4;
		congruence_inc_4();
		// OEIS A114809: in our range, all abundant number should be divisible by 3 or 7
		if(congruence[0]==0){
			factor_init();
			trial_factor_5();
			check_weird();
		}
		// residue: 25 -> 27
		n+=2;
		congruence_inc_2();
		factor_init();
		trial_factor_3();
		check_weird();
		pcnt++;
		if(pcnt==50000000){
			pcnt=0;
			printf("Checked to %lu\n", n);
			fio=fopen("ckpt.txt","w");
			fprintf(fio,"%lu %lu",n,checksum);
			fclose(fio);
		}
	}
	return 0;
}
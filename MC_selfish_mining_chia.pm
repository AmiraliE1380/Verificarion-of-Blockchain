dtmc

// x is fraction of space controlled by adv.
const double x = 0.2;
// d is the max lead the adv can have
const int d = 6;
// at each depth 6 private blocks can be saved.
const int w = 6;


// n is total number of private adv. blocks	
formula n = (n0+n1+n2+n3+n4+n5+n6);
formula total = (n*x+1);

module SelfishMiningChia

	
	// ni is the number of private blocks at level i
	n0 : [0..w] init 0;
	n1 : [0..w] init 0;
	n2 : [0..w] init 0;
	n3 : [0..w] init 0;
	n4 : [0..w] init 0;
	n5 : [0..w] init 0;
	n6 : [0..w] init 0;
	
	
	// rewards
	adv : [0..2] init 0;
	honest : [0..2] init 0;


	[] n0=0 & n1=0 -> x : (n1'=1) & (adv'=0) & (honest'=0) +
			(1-x) : (adv'=0) & (honest'=1);


	[] n0>0 & n1=0 -> n0*x/((n0-1)*x+1) : (n0'=0) & (adv'=2) & (honest'=0) +
			n0*(1-x)/((n0+1)*((n0-1)*x+1)) : (n0'=0) & (adv'=1) & (honest'=1) +
			(1-x)/((n0+1)*((n0-1)*x+1)) : (n0'=0) & (adv'=0) & (honest'=2);


	[] n1>0 & n2=0 -> (1-x)/total : (n0'=n1) & (n1'=0) & (adv'=0) & (honest'=0) +
			(n0+1)*x/total : (n1'=min(w,n1+1)) & (adv'=0) & (honest'=0) +
			n1*x/total : (n2'=min(w,n2+1)) & (adv'=0) & (honest'=0) +
			n2*x/total : (n3'=min(w,n3+1)) & (adv'=0) & (honest'=0) +
			n3*x/total : (n4'=min(w,n4+1)) & (adv'=0) & (honest'=0) +
			n4*x/total : (n5'=min(w,n5+1)) & (adv'=0) & (honest'=0) +
			n5*x/total : (n6'=min(w,n6+1)) & (adv'=0) & (honest'=0) +
			n6*x/total : (n0'=n1) & (n1'=n2) & (n2'=n3) & (n3'=n4) &
					(n4'=n5) & (n5'=n6) & (n6'=1) & (adv'=1)
					& (honest'=0);
			
	

	[] n2>0 & n3=0 -> (1-x)/total : (n0'=0) & (n1'=0) & (n2'=0) & (adv'=2) & (honest'=0) +
			(n0+1)*x/total : (n1'=min(w,n1+1)) & (adv'=0) & (honest'=0) +
			n1*x/total : (n2'=min(w,n2+1)) & (adv'=0) & (honest'=0) +
			n2*x/total : (n3'=min(w,n3+1)) & (adv'=0) & (honest'=0) +
			n3*x/total : (n4'=min(w,n4+1)) & (adv'=0) & (honest'=0) +
			n4*x/total : (n5'=min(w,n5+1)) & (adv'=0) & (honest'=0) +
			n5*x/total : (n6'=min(w,n6+1)) & (adv'=0) & (honest'=0) +
			n6*x/total : (n0'=n1) & (n1'=n2) & (n2'=n3) & (n3'=n4) &
					(n4'=n5) & (n5'=n6) & (n6'=1) & (adv'=1)
					& (honest'=0);


	[] n3>0 -> (1-x)/total : (n0'=n1) & (n1'=n2) & (n2'=n3) & (n3'=n4) & (n4'=n5)
					& (n5'=n6) & (n6'=0) & (adv'=1) & (honest'=0) +
			(n0+1)*x/total : (n1'=min(w,n1+1)) & (adv'=0) & (honest'=0) +
			n1*x/total : (n2'=min(w,n2+1)) & (adv'=0) & (honest'=0) +
			n2*x/total : (n3'=min(w,n3+1)) & (adv'=0) & (honest'=0) +
			n3*x/total : (n4'=min(w,n4+1)) & (adv'=0) & (honest'=0) +
			n4*x/total : (n5'=min(w,n5+1)) & (adv'=0) & (honest'=0) +
			n5*x/total : (n6'=min(w,n6+1)) & (adv'=0) & (honest'=0) +
			n6*x/total : (n0'=n1) & (n1'=n2) & (n2'=n3) & (n3'=n4) &
					(n4'=n5) & (n5'=n6) & (n6'=1) & (adv'=1)
					& (honest'=0);


endmodule

rewards "adv"
    	[] true : honest;
    	//[] true : adv;
endrewards

mdp

// formulae 
// left fork free (left neighbour is philosopher 2)
//formula lfree = (p2>=0 & p2<=4) | p2=6 | p2=10;
// right fork free (left neighbour is philosopher 3)
//formula rfree = (p3>=0 & p3<=3) | p3=5 | p3=7 | p3=11;

// x is fraction of space controlled by adv.
const double x = 0.05;

// di is the max deapth of tree i
const int d1 = 5;
const int d2 = 4;
const int d3 = 3;
const int d4 = 3;

// wi is the max width of tree i
const int w1 = 2;
const int w2 = 2;
const int w3 = 2;
const int w4 = 2;


// n is total number of blocks adv. mines on, including 4 blocks in the public chain
formula n = (n11+n12+n13+n14+n21+n22+n23+n31+n32+n41+n42+4);
formula total = ((n - 1)*x+1); // total mining power of the network


module selfish_mining_general_strategy

 	// nij is the number of private blocks in tree i at level j
 	n11 : [0..w1] init 0;
 	n12 : [0..w1] init 0;
 	n13 : [0..w1] init 0;
 	n14 : [0..w1] init 0;
 	n15 : [0..w1] init 0;
  
 	n21 : [0..w2] init 0;
	n22 : [0..w2] init 0;
	n23 : [0..w2] init 0;
 	n24 : [0..w2] init 0;
  
 	n31 : [0..w3] init 0;
  	n32 : [0..w3] init 0;
  	n33 : [0..w3] init 0;
  
 	n41 : [0..w4] init 0;
  	n42 : [0..w4] init 0;
  	n43 : [0..w4] init 0;
  
  	// bi is the status of the public block at deapth 3 - i
  	// if bi=0 the block belongs to honest miner, if bi=1 it belongs to the selfish miner
  	b1 : [0..1] init 0;
  	b2 : [0..1] init 0;
  	b3 : [0..1] init 0;

  	// fb1,...,fb5 are blocks finilized in the main chain, fbi=1 meand it's adversarial
  	fb1 : [0..1] init 0;
  	fb2 : [0..1] init 0;
  	fb3 : [0..1] init 0;
  	fb4 : [0..1] init 0;
  	fb5 : [0..1] init 0;
  
  	// act=1 specifies states where selfish miner can make a decision (publishing a tree or nothing)
  	act : [0..1] init 0;

  	// honest_mined=1 iff the last mined block is honest
  	honest_mined : [0..1] init 0;

  	[] act=0 -> (1-x)/total : (honest_mined'=1) & (act'=1) +
      		1*x/total : (n11'=min(w1,n11+1)) & (act'=1) +
      		n11*x/total : (n12'=min(w1,n12+1)) & (act'=1) +
      		n12*x/total : (n13'=min(w1,n13+1)) & (act'=1) +
      		n13*x/total : (n14'=min(w1,n14+1)) & (act'=1) +
      		n14*x/total : (n15'=min(w1,n15+1)) & (act'=1) +
      
      	1*x/total : (n21'=min(w2,n21+1)) & (act'=1) +
      		n21*x/total : (n22'=min(w2,n22+1)) & (act'=1) +
      		n22*x/total : (n23'=min(w2,n23+1)) & (act'=1) +
      		n23*x/total : (n24'=min(w2,n24+1)) & (act'=1) +
      
      	1*x/total : (n31'=min(w3,n31+1)) & (act'=1) +
      		n31*x/total : (n32'=min(w3,n32+1)) & (act'=1) +
      		n32*x/total : (n33'=min(w3,n33+1)) & (act'=1) +
      
      	1*x/total : (n41'=min(w4,n41+1)) & (act'=1) +
      		n41*x/total : (n12'=min(w4,n42+1)) & (act'=1) +
      		n42*x/total : (n13'=min(w4,n43+1)) & (act'=1);
  


  	[] act=1 & honest_mined=0 -> (act'=0); //does not publish


	//tree 4
  	//publish a block from t4
  	[] act=1 & n41>0 & honest_mined=0 -> (act'=0) & (fb5'=fb4) & (fb4'=fb3) & (fb3'=fb2) & (fb2'=fb1) & (fb1'=b1) &
		(b1'=b2) & (b2'=b3) & (b3'=1) &
      		(n11'=n21) & (n12'=n22) & (n13'=n23) & (n14'=n24) & (n15'=0) &
      		(n21'=n31) & (n22'=n32) & (n23'=n33) & (n24'=0) &
      		(n31'=n41-1) & (n32'=0) & (n33'=0) & 
      		(n41'=min(1,n42)) & (n42'=min(1, n43)) & (n43'=0); //correct!!!!!!!

  	//publish 2 blocks from t4
  	[] act=1 & n42>0 & honest_mined=0 -> (act'=0) & (fb5'=fb3) & (fb4'=fb2) & (fb3'=fb1) & (fb2'=b1) & (fb1'=b2) &
		(b1'=b3) & (b2'=1) & (b3'=1) &
      		(n11'=n31) & (n12'=n32) & (n13'=n33) & (n14'=0) & (n15'=0) &
      		(n21'=n41-1) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) &
     		(n41'=min(1,n43)) & (n42'=0) & (n43'=0);  //correct!!!!!!!

  	//publish 3 blocks from t4
  	[] act=1 & n43>0 & honest_mined=0 -> (act'=0) & (fb5'=fb2) & (fb4'=fb1) & (fb3'=b1) & (fb2'=b2) & (fb1'=b3) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=n41-1) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) & 
      		(n41'=0) & (n42'=0) & (n43'=0);  //correct!!!!!!!




	//tree 3
  	//publish 2 blocks from t3
  	[] act=1 & n32>0 & honest_mined=0 -> (act'=0) & (fb5'=fb4) & (fb4'=fb3) & (fb3'=fb2) & (fb2'=fb1) & (fb1'=b1) &
		(b1'=b2) & (b2'=1) & (b3'=1) &
      		(n11'=n21) & (n12'=n22) & (n13'=n23) & (n14'=n24) & (n15'=0) &
      		(n21'=n31-1) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) &
     		(n41'=min(1,n33)) & (n42'=0) & (n43'=0); //correct!!!!!!!

  	//publish 3 blocks from t3
  	[] act=1 & n33>0 & honest_mined=0 -> (act'=0) & (fb5'=fb3) & (fb4'=fb2) & (fb3'=fb1) & (fb2'=b1) & (fb1'=b2) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=n31-1) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) & 
      		(n41'=0) & (n42'=0) & (n43'=0);  //correct!!!!!!!





	//tree 2
  	//publish 3 blocks from t2
  	[] act=1 & n23>0 & honest_mined=0 -> (act'=0) & (fb5'=fb4) & (fb4'=fb3) & (fb3'=fb2) & (fb2'=fb1) & (fb1'=b1) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=n21-1) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) &
     		(n41'=min(1,n24)) & (n42'=0) & (n43'=0);

  	//publish 4 blocks from t2
  	[] act=1 & n24>0 & honest_mined=0 -> (act'=0) & (fb5'=fb3) & (fb4'=fb2) & (fb3'=fb1) & (fb2'=b1) & (fb1'=1) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=0) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) & 
      		(n41'=0) & (n42'=0) & (n43'=0); 

  
    

	//tree 1
  	//publish 4 blocks from t1
  	[] act=1 & n14>0 & honest_mined=0 -> (act'=0) & (fb5'=fb4) & (fb4'=fb3) & (fb3'=fb2) & (fb2'=fb1) & (fb1'=1) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=0) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) &
     		(n41'=min(1, n15)) & (n42'=0) & (n43'=0);

  	//publish 5 blocks from t1
  	[] act=1 & n15>0 & honest_mined=0 -> (act'=0) & (fb5'=fb3) & (fb4'=fb2) & (fb3'=fb1) & (fb2'=1) & (fb1'=1) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=0) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) & 
      		(n41'=0) & (n42'=0) & (n43'=0); 

  
    


  	//consider the states where honest_mined=1
	
	// adversary does not publish in response to honest miners
	[] act=1 & honest_mined=1 -> (act'=0) & (honest_mined'=0) &
		(fb5'=fb4) & (fb4'=fb3) & (fb3'=fb2) & (fb2'=fb1) & (fb1'=b1) &
		(b1'=b2) & (b2'=b3) & (b3'=0) &
      		(n11'=n21) & (n12'=n22) & (n13'=n23) & (n14'=n24) & (n15'=0) &
      		(n21'=n31) & (n22'=n32) & (n23'=n33) & (n24'=0) &
      		(n31'=n41) & (n32'=n42) & (n33'=n43) & 
      		(n41'=0) & (n42'=0) & (n43'=0); //correct!!!!!!!

	// advarsary can release 2 blocks from t4
	[] act=1 & n42>0 & honest_mined=1 -> (act'=0) & (honest_mined'=0) &
		(fb5'=fb3) & (fb4'=fb2) & (fb3'=fb1) & (fb2'=b1) & (fb1'=b2) &
		(b1'=b3) & (b2'=1) & (b3'=1) &
      		(n11'=n31) & (n12'=n32) & (n13'=n33) & (n14'=0) & (n15'=0) &
      		(n21'=n41-1) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) &
     		(n41'=min(1,n43)) & (n42'=0) & (n43'=0);  //correct!!!!!!!
	
	// advarsary can release 3 blocks from t4
	[] act=1 & n43>0 & honest_mined=1 -> (act'=0) & (honest_mined'=0) &
		(fb5'=fb2) & (fb4'=fb1) & (fb3'=b1) & (fb2'=b2) & (fb1'=b3) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=n41-1) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) & 
      		(n41'=0) & (n42'=0) & (n43'=0);  //correct!!!!!!!

	//  advarsary can release 3 blocks from t3
	[] act=1 & n33>0 & honest_mined=1 -> (act'=0) & (honest_mined'=0) &
		(fb5'=fb3) & (fb4'=fb2) & (fb3'=fb1) & (fb2'=b1) & (fb1'=b2) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=n31-1) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) & 
      		(n41'=0) & (n42'=0) & (n43'=0);  //correct!!!!!!!

	//  advarsary can release 4 blocks from t2
  	[] act=1 & n24>0 & honest_mined=1 -> (act'=0) & (honest_mined'=0) &
		(fb5'=fb3) & (fb4'=fb2) & (fb3'=fb1) & (fb2'=b1) & (fb1'=1) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=0) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) & 
      		(n41'=0) & (n42'=0) & (n43'=0); 

	//publish 5 blocks from t1
  	[] act=1 & n15>0 & honest_mined=1 -> (act'=0) & (honest_mined'=0) &
		(fb5'=fb3) & (fb4'=fb2) & (fb3'=fb1) & (fb2'=1) & (fb1'=1) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=0) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) & 
      		(n41'=0) & (n42'=0) & (n43'=0); 

	

endmodule

rewards
      	//[] true : honest;
      	//[] finilize_block=1 : adv;
  	//instead of true, you can write another gaurd
	[] true : (fb1+fb2+fb3+fb4+fb5)/5;
endrewards
mdp

// x is fraction of space controlled by adv.
const double x = 0.2;
//y or gamma is the probability of honest mining on adv blocks during a race condition
const double y = 0.5;
//cq is chain quality, will initially be set to 0.5 and will estimate the real value after 10 steps
const double cq = 0.5;


// di is the max deapth of chains/branches at deapth 4-i of the public chain
const int d1 = 5;
const int d2 = 4;
const int d3 = 3;
const int d4 = 3;


// n is total number of blocks adv. mines on, including 4 blocks in the public chain
formula n = (4+min(c11+c12,1)+min(c21+c22,1)+min(c31+c32,1)+min(c41+c42,1)); // number of blocks adv mines on top of
formula total = ((n - 1)*x+1); // total mining power of the network  //TODO: change this


module selfish_mining_general_strategy

 	// cij is the jth private chain at deapth 4-i
 	c11 : [0..d1] init 0;
 	c12 : [0..d1] init 0;
 	
 	c21 : [0..d2] init 0;
 	c22 : [0..d2] init 0;
 	
 	c31 : [0..d3] init 0;
 	c32 : [0..d3] init 0;
 	
 	c41 : [0..d4] init 0;
 	c42 : [0..d4] init 0;
 	
  	// bi is the status of the public block at deapth 3 - i
  	// if bi=0 the block belongs to honest miner, if bi=1 it belongs to the selfish miner
  	b1 : [0..1] init 0;
  	b2 : [0..1] init 0;
  	b3 : [0..1] init 0;


  	// act=1 specifies states where selfish miner can make a decision (publishing a tree or nothing)
  	act : [0..1] init 0;

  	// honest_mined=1 iff the last mined block is honest
  	honest_mined : [0..1] init 0;

	// adv and honest are the number of adv and honest finilized blocks in a transition
	honest : [0..3] init 0;
	adv : [0..3] init 0;
	


  	[] act=0 -> (1-x)/total : (honest_mined'=1) & (act'=1) & (adv'=0) & (honest'=0);
	

	[] act=0 & c11=0 -> 1*x/total : (c11'=1) & (act'=1) & (adv'=0) & (honest'=0);

	[] act=0 & c11>0 -> 1*x/total : (c11'=min(d1,c11+1)) & (act'=1) & (adv'=0) & (honest'=0) +
			1*x/total : (c12'=min(d1,c12+1)) & (act'=1) & (adv'=0) & (honest'=0);
	

	[] act=0 & c21=0 -> 1*x/total : (c21'=1) & (act'=1) & (adv'=0) & (honest'=0);

	[] act=0 & c21>0 -> 1*x/total : (c21'=min(d2,c21+1)) & (act'=1) & (adv'=0) & (honest'=0) +
			1*x/total : (c22'=min(d2,c22+1)) & (act'=1) & (adv'=0) & (honest'=0);
	
	
	[] act=0 & c31=0 -> 1*x/total : (c31'=1) & (act'=1) & (adv'=0) & (honest'=0);

	[] act=0 & c31>0 -> 1*x/total : (c31'=min(d3,c31+1)) & (act'=1) & (adv'=0) & (honest'=0) +
			1*x/total : (c32'=min(d3,c32+1)) & (act'=1) & (adv'=0) & (honest'=0);
	

	[] act=0 & c41=0 -> 1*x/total : (c41'=1) & (act'=1) & (adv'=0) & (honest'=0);

	[] act=0 & c41>0 -> 1*x/total : (c41'=min(d4,c41+1)) & (act'=1) & (adv'=0) & (honest'=0) +
			1*x/total : (c42'=min(d4,c42+1)) & (act'=1) & (adv'=0) & (honest'=0);
	

	// TODO: MAYBE NEED TO CHANGE THIS
  	[] act=1 & honest_mined=0 -> (act'=0); //does not publish



	// branch 41 //Done!
	// publish a block from branch 41
	[] act=1 & & honest_mined=0 & c41>0 -> (act'=0) & (adv'=b0) & (honest'=1-b0) & (b1'=b2) & (b2'=b3) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c42) & (c32'=0) & (c41'=c41-1) & (c42'=0);

	// publish 2 blocks from branch 41
	[] act=1 & & honest_mined=0 & c41>1 -> (act'=0) & (adv'=b0+b1) & (honest'=2-(b0+b1)) & (b1'=b3) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=c32) & (c21'=c42) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-2) & (c42'=0);

	// publish 3 blocks from branch 41
	[] act=1 & & honest_mined=0 & c41>2 -> (act'=0) & (adv'=b0+b1+b2) & (honest'=3-(b0+b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c42) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);




	// branch 42 //Done!
	// publish a block from branch 42
	[] act=1 & & honest_mined=0 & c42>0 -> (act'=0) & (adv'=b0) & (honest'=1-b0) & (b1'=b2) & (b2'=b3) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=0) & (c41'=c42-1) & (c42'=0);

	// publish 2 blocks from branch 42
	[] act=1 & & honest_mined=0 & c42>1 -> (act'=0) & (adv'=b0+b1) & (honest'=2-(b0+b1)) & (b1'=b3) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-2) & (c42'=0);

	// publish 3 blocks from branch 42
	[] act=1 & & honest_mined=0 & c42>2 -> (act'=0) & (adv'=b0+b1+b2) & (honest'=3-(b0+b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c41) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);




	// branch 31
	// publish the single block of branch 31
	[] act=1 & & honest_mined=0 & c31=0 -> y : (act'=0) & (b3'=1) & (c31'=0) & (c41'=c31-1) & (c42'=0) +
			1-y : ; //maybe wrong

	// publish a block from branch 31
	[] act=1 & & honest_mined=0 & c31>0 -> (act'=0) & (adv'=b0) & (honest'=1-b0) & (b1'=b2) & (b2'=b3) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c42) & (c32'=0) & (c41'=c41-1) & (c42'=0);

	// publish 2 blocks from branch 31
	[] act=1 & & honest_mined=0 & c31>1 -> (act'=0) & (adv'=b0) & (honest'=1-b0) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=c32) & (c21'=c42) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-2) & (c42'=0);

	// publish 3 blocks from branch 41
	[] act=1 & & honest_mined=0 & c41>2 -> (act'=0) & (adv'=b0+b1+b2) & (honest'=3-(b0+b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c42) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);













	//tree 4
  	//publish a block from t4
  	[] act=1 & n41>0 & honest_mined=0 -> (act'=0) & (fb5'=fb4) & (fb4'=fb3) & (fb3'=fb2) & (fb2'=fb1) & (fb1'=b1) &
		(b1'=b2) & (b2'=b3) & (b3'=1) &
      		(n11'=n21) & (n12'=n22) & (n13'=n23) & (n14'=n24) & (n15'=0) &
      		(n21'=n31) & (n22'=n32) & (n23'=n33) & (n24'=0) &
      		(n31'=max(0,n41-1)) & (n32'=0) & (n33'=0) & 
      		(n41'=min(1,n42)) & (n42'=min(1, n43)) & (n43'=0); //correct!!!!!!!

  	//publish 2 blocks from t4
  	[] act=1 & n42>0 & honest_mined=0 -> (act'=0) & (fb5'=fb3) & (fb4'=fb2) & (fb3'=fb1) & (fb2'=b1) & (fb1'=b2) &
		(b1'=b3) & (b2'=1) & (b3'=1) &
      		(n11'=n31) & (n12'=n32) & (n13'=n33) & (n14'=0) & (n15'=0) &
      		(n21'=max(0,n41-1)) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) &
     		(n41'=min(1,n43)) & (n42'=0) & (n43'=0);  //correct!!!!!!!

  	//publish 3 blocks from t4
  	[] act=1 & n43>0 & honest_mined=0 -> (act'=0) & (fb5'=fb2) & (fb4'=fb1) & (fb3'=b1) & (fb2'=b2) & (fb1'=b3) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=max(0,n41-1)) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) & 
      		(n41'=0) & (n42'=0) & (n43'=0);  //correct!!!!!!!




	//tree 3
  	//publish 2 blocks from t3
  	[] act=1 & n32>0 & honest_mined=0 -> (act'=0) & (fb5'=fb4) & (fb4'=fb3) & (fb3'=fb2) & (fb2'=fb1) & (fb1'=b1) &
		(b1'=b2) & (b2'=1) & (b3'=1) &
      		(n11'=n21) & (n12'=n22) & (n13'=n23) & (n14'=n24) & (n15'=0) &
      		(n21'=max(0,n31-1)) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) &
     		(n41'=min(1,n33)) & (n42'=0) & (n43'=0); //correct!!!!!!!

  	//publish 3 blocks from t3
  	[] act=1 & n33>0 & honest_mined=0 -> (act'=0) & (fb5'=fb3) & (fb4'=fb2) & (fb3'=fb1) & (fb2'=b1) & (fb1'=b2) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=max(0,n31-1)) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) & 
      		(n41'=0) & (n42'=0) & (n43'=0);  //correct!!!!!!!





	//tree 2
  	//publish 3 blocks from t2
  	[] act=1 & n23>0 & honest_mined=0 -> (act'=0) & (fb5'=fb4) & (fb4'=fb3) & (fb3'=fb2) & (fb2'=fb1) & (fb1'=b1) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=max(0,n21-1)) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
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
      		(n21'=max(0,n41-1)) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) &
     		(n41'=min(1,n43)) & (n42'=0) & (n43'=0);  //correct!!!!!!!
	
	// advarsary can release 3 blocks from t4
	[] act=1 & n43>0 & honest_mined=1 -> (act'=0) & (honest_mined'=0) &
		(fb5'=fb2) & (fb4'=fb1) & (fb3'=b1) & (fb2'=b2) & (fb1'=b3) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=max(0,n41-1)) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
      		(n21'=0) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) & 
      		(n41'=0) & (n42'=0) & (n43'=0);  //correct!!!!!!!

	//  advarsary can release 3 blocks from t3
	[] act=1 & n33>0 & honest_mined=1 -> (act'=0) & (honest_mined'=0) &
		(fb5'=fb3) & (fb4'=fb2) & (fb3'=fb1) & (fb2'=b1) & (fb1'=b2) &
		(b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=max(0,n31-1)) & (n12'=0) & (n13'=0) & (n14'=0) & (n15'=0) &
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
	//[] true : (fb1+fb2+fb3+fb4+fb5)/5;
	[] honest>0 : honest * (-b);
	[] adv>0 : adv * (1-b); 
endrewards
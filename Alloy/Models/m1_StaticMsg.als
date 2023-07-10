/*************************************
 *  Model 1 for OpenThread Protocol  *
 *************************************/

/* 
   - Node Types:
 	FTD - Full Thread Device 		
 	MTD - Minimal Thread device 

    - Node Roles:
	> FTD can be:
	 	FED-Full End Device
	  	REED-Router Eligible End Device {Router, BorderRouter,Leader, or none(temporarily) }
	> MTD can be:
	 	MED- Minimal End Device
	 	SED-Sleepy End Device

    -Messages types

	Discovering(active scan):
		-beacon (Request /response) - é enviado para um canal especifico , 
		  						No entanto este processo é realizado para todos os canais.
	Create a new partition:
		- MLE adertisements  - de seguida serão enviados estas msg , para informar o estado do link e tb responde a possiveis 
		   becon requests  de novos dipositivos no active scan (is seleted a least busy channel) 
	Joining in one partition : 
		- Parent Request - é enviada em multicast para todos os seus vizinhos ao alcance, para descobrir routers ou REED 
		- Parent Response - os routers respondem as msg(Os REED podem ser excluidos do scan - param configuravel 
		- Child ID Request - pedido enviado para o router para ser o seu filho
		-Child ID Response - resposta do router.
	Establish bi-directional Router-Router links:
		-Link Request (Multicast) candidato envia msg a todos os nós à volta.
		-Link Accept and Request - Resposta dos router em unicast ao candidato a dizer que podem aceitar conexões
		-Link Accept - o candidato aceita  os router que pretende fazer a ligação.
	Maintenance(Processo periodico):
		- MLE Advertisements 
		- (DynamicRoutes) 
		 
*/

abstract sig Role{}
one sig REED,Router,Leader extends Role {}

abstract sig Node{
	var role : one Role,
	var inbox: set Message,  
	var partition_id:set Partition,
	in_range:set Node
}
sig FTD extends Node{}

sig MTD extends Node{}

sig Partition{
	var leader: set Node,
}

fun elems:Partition ->Node{
 	~partition_id
}

abstract sig Message {
	from : one Node
}

sig  Preq,Presp,Creq,Lreq,LAreq,LAresp extends Message {}

sig Cresp , Adv extends Message {
	part_id: one Partition
}

/*************************************
 *          System Specification          *
 *************************************/

//In the initial state, there are no leaders, partitions and messages
fact Init
{	no inbox
	no partition_id
	no leader
	no (Node.role &Leader)
}

//Note:in_Range is reflexive and does not contain the identity
fact Common_configuration
{
	~in_range in in_range
	no (in_range & iden)
}


fact FTD_configuration 
{
	// Every device, router-capable or not, initially attaches to a Thread network as a Child (End Device).
	all n:FTD | n.role = REED
}



fact MTD_configuration { }



// No repeated messages
fact Unique{
	all disj a,b : Cresp  | a.from !=b.from or a.part_id != b.part_id
	all disj a,b : Adv  | a.from !  =b.from or a.part_id != b.part_id
	all disj a,b :Message- (Cresp + Adv ) |   a.from !=b.from 
}





/*************************************
 *                 Transitions       *
 *************************************/

pred Nop{
	role'=role
	inbox'=inbox
	leader'=leader
	elems'=elems
}

// Messages handling - Send messages
pred send[m:Message, nd_from:Node, nd_to:set Node,del_msg : set Message]{
	m.from'=nd_from
	
	nd_from.inbox'= nd_from.inbox - del_msg
	all n : nd_to | n.inbox'= n.inbox + m
	all n:Node-(nd_to+nd_from)| n.inbox'=n.inbox
}
// Messages handling - Delete messages
pred delete[m:set Message,nd_to:Node]{
	
	all n : nd_to | n.inbox'= n.inbox - m
	all n:Node-nd_to | n.inbox'=n.inbox
}



/*
	1- Request to ask a router to be the father (Multicast) 
	(x2 on max-If a router does not respond, the device will assume that it is the first node and form a singleton network, consisting only of a Leader. This is done by sending out the data response, followed by beginning advertisement)
	MLE_PARENT_REQ_SCANMASK_R_TIMEOUT = 0.75sec (responses for routers)
	MLE_PARENT_REQ_SCANMASK_RE_TIMEOUT = 1.25sec (REEDs or routers)
*/
pred send_ParentRequest [n :Node] {
	some m : Preq | send[m,n,n.in_range,none] 

	role'=role
	partition_id'=partition_id	
	leader'=leader
}



// 2- Router response for the candidate child. (Unicast)
pred send_ParentResponse [n :FTD] {
	// O Ftd já está numa partiçao
	some n.partition_id
	some m : Presp,  msg: (n.inbox & Preq)  | send[m,n,msg.from,msg] 

	role'=role
	partition_id'=partition_id	
	leader'=leader
}

/*
	3- Send request to a specific father 
	When attaching to a Parent, an end device first attempts to find a suitable Router within one
	hop of itself. If that fails, it then chooses a REED within one hop and requests that the REED
	become device router.
*/

pred send_ChildRequest [n :Node] {
	some m : Creq',  msg: (n.inbox & Presp)  | send[m,n,msg.from, msg] 

	role'=role
	partition_id'=partition_id	
	leader'=leader
}

// 4- The father accepts the son
pred send_ChildResponse [n :FTD] {
	one n.partition_id
	some m : Cresp,  msg: (n.inbox & Creq)  | msg.part_id=n.partition_id and send[m,n,msg.from, msg] 
			
	role'=role
	partition_id'=partition_id	
	leader'=leader
}

----------

pred changed_to_leader[n:FTD]{
	no n.partition_id
	role '= role - (n->n.role) + (n->Leader) // Becomes leader

	some p:Partition{
		no p.elems
		partition_id'=partition_id	+(n->p) - (n->n.partition_id)
		leader'=leader + (p->n)
	}
	
	inbox'=inbox
}



pred reset[n:Node]{
	n.role'=REED
	no n.partition_id'
	all nd:Node -n |{
		nd.partition_id'=nd.partition_id
		nd.role'=nd.role
	}
	leader'= leader - (n.partition_id->n)
	delete[n.inbox,n] // Clean my inbox
}




pred join_to_partition[n:Node]{
	some msg: (n.inbox & Cresp) | {
		msg.from in n.in_range 
		partition_id'=partition_id	+ (n-> msg.part_id) -  (n->n.partition_id)
		delete[msg,n]
	}
	 
 	n in FTD => role'=role - (n->n.role) +(n->REED) 
		     else role'=role 
	leader'=leader - (Partition -> n) // If the node is leader of any partition it ceases to be.
	
}

// Multicast message
pred send_Advertisement[n:FTD]{
	n.role in (Leader +Router)
	some n.in_range
	some m : Adv | m.part_id= n.partition_id and  send[m,n,n.in_range,none] 
	
	role'=role
	partition_id'=partition_id	
	leader'=leader
}

pred merge_partitions[n:FTD]{
	some n.partition_id
	some msg: (n.inbox & Adv)  | {		
		no (msg.part_id & n.partition_id )=>remove_elemPartition[ n.partition_id,n,msg.part_id]  and role'=role -  (n->n.role ) + (n->REED )
							else( partition_id'=partition_id and leader'=leader  and role'=role)
		delete[msg,n] 
	} 
}

pred remove_elemPartition[old_parts:one Partition,node:set Node,newPart:one Partition]{
	some (old_parts.leader & node ) => leader'=leader - (old_parts->node) else  leader'=leader
	partition_id'=partition_id -(node->old_parts) + (node->newPart)
}



/* 	 	Link Establishment Process Between Routers		*/



// Sent in multicast to all routers
pred send_LinkRequest[n:FTD]{
	n.role in REED
	one n.partition_id

	some m : Lreq | send[m,n,(n.in_range & role.(REED + Router+Leader)),none] 

	role'=role
	partition_id'=partition_id	
	leader'=leader
}


pred send_LinkAcceptReq[n:FTD]{
	one n.partition_id

	some m : LAreq ,  msg: (n.inbox & Lreq)  | send[m,n,msg.from, msg] 

	role'=role
	partition_id'=partition_id	
	leader'=leader
}


pred send_LinkAcceptResp[n:FTD]{
	one n.partition_id

	some m : LAresp ,  msg: (n.inbox & LAreq)  | send[m,n,msg.from,msg] 

	role'=role - (n->n.role) + (n->Router)
	partition_id'=partition_id	
	leader'=leader
}


/*************************************
 *                 Simulation                 *
 *************************************/


fact transitions{
	always (Nop or 
			some n:Node |{
				send_ParentRequest[n] or send_ChildRequest[n] or
				join_to_partition[n] or
				reset[n]
				
			} or 
			some  ftd:FTD|{			
				send_ParentResponse[ftd] or  send_ChildResponse[ftd] or 
				changed_to_leader[ftd] or
				send_LinkRequest[ftd] or send_LinkAcceptReq[ftd] or send_LinkAcceptResp[ftd] or 
				send_Advertisement[ftd] or merge_partitions[ftd] 
			} 
		    )
}



/*
run{ 
	#Node = 2 
	#FTD =2 
	some in_range
} for  10 but 0 int
*/



/*************************************
 *                 Fairness                    *
 *************************************/
pred sendAdvEnable[n:FTD]{
	n.role in (Leader +Router)
	some n.in_range
}

pred merge_partitionEnabled[n:Node] {
	some n.partition_id
	some (n.inbox & Adv) 
}

pred changeToLeaderEnabled[n:FTD]{
	no n.partition_id
}

pred joinToPartitionEnabled[n:Node]{
	some (n.inbox & Cresp)
}


pred send_ParentRequestEnabled[n:Node]{

}



pred send_ParentResponseEnabled[n:FTD]{
	some n.partition_id
	some (n.inbox & Preq)

}

pred send_ChildRequestEnabled [n:Node]{
	some (n.inbox & Presp) 
}


pred send_ChildResponseEnabled[n:FTD]{
	some n.partition_id
	some (n.inbox & Creq) 

}

pred fairness {
	all  n:FTD| {
		eventually always sendAdvEnable[n] implies always eventually send_Advertisement[n]
		eventually always changeToLeaderEnabled[n] implies always eventually changed_to_leader[n]
		eventually always send_ParentResponseEnabled[n] implies always eventually send_ParentResponse[n]
		eventually always send_ChildResponseEnabled[n] implies always eventually send_ChildResponse[n]
	}
	all n:Node |{
		eventually always merge_partitionEnabled[n] implies always eventually merge_partitions[n]
		eventually always joinToPartitionEnabled[n] implies always eventually join_to_partition[n]
		always eventually send_ParentRequest[n]
		eventually always send_ChildRequestEnabled[n] implies always eventually send_ChildRequest[n]
	}
}	


/*************************************
 *      Proprieties to be checked    *
 *************************************/
check lonePartition {
	always all n:Node | lone n.partition_id
}for   3 but  exactly  3 Partition,  8 Message, 0 int, 9 steps

check  greedyLeader{
	always all p:Partition | lone p.leader  

}for  3 but  exactly  4 Partition,  8 Message, 0 int, 9 steps


// Liveness
check convergeToOnePartition{
 	fairness  and some FTD and  (all n:Node | (Node-n) in n.^in_range  and eventually always not reset[n]) =>  eventually  always (some p:Partition | Node in p.elems)  
} for  3 but  exactly 3 Partition,  8 Message, 0 int, 9 steps





/*************************************
 *           Theme Functions              *
 *************************************/
fun reed : set Node  { 
	role.REED 
}
fun router : set Node  { 
	role.Router
}
fun th_leader:set Node{
	role.Leader
}


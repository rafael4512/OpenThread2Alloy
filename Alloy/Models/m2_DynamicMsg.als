/*************************************
 *  Model 2 for OpenThread Protocol  *
 *************************************/

/* 
   - Node Types:
 	FTD - Full Thread Device 		
 	MTD - Minimal Thread device 

    - Node Roles:
	> FTD can be:
	 	FED-Full End Device
	  	REED-Router Eligible End Device {Router, BorderRouter,Leader, or none(temporarily) }
	> MTD can be:// Na spec  é referido como End Device 
		(An End Device normally only sends and receives messages via its Parent)
	 	MED- Minimal End Device
	 	SED-Sleepy End Device

    -Messages types

	Create a new partition:
		- MLE adertisements  - de seguida serão enviados estas msg , para informar o estado do link e tb responde a possiveis 
		   becon requests  de novos dipositivos no active scan (is seleted a least busy channel) 
	Joining in one partition : 
		- Parent Request - é enviada em multicast para todos os seus vizinhos ao alcance, para descobrir routers ou REED 
		- Parent Response - os routers respondem as msg(Os REED podem ser excluidos do scan - param configuravel 
		- Child ID Request - pedido enviado para o router para ser o seu filho
		-Child ID Response - resposta do router.
	Establish bi-directional Router-Router links:( when occurs - 4.7.7)
		-Link Request (Multicast) candidato envia msg a todos os Router E REEDS à volta.
		-Link Accept and Request - Resposta dos router em unicast ao candidato a dizer que podem aceitar conexões
		-Link Accept - o candidato aceita  os router que pretende fazer a ligação.
	Maintenance(Processo periodico):
		- MLE Advertisements 
		- (DynamicRoutes) 
		 
	
   - Networks discover - commissioning 
	(The commissioning has already been successfully performed, the device has already been associated with a threadNetwork)
	Thread Spec - page 218

*/

//Roles
abstract sig Role{}
one sig REED,Router,Leader extends Role {}
 
//Nodes
abstract sig Node{
	var role : one Role,
	var inbox: set Message,  
	var partition_id:set Partition, 
	in_range:set Node 

}
sig FTD extends Node{
	//var childs: set Node, 
	//var connected_ds:set Router, 
	//routing_table: Node( next_hop) -> Node (destino)	
}

sig MTD extends Node{ 
	//var parent: lone Node,
}


//Network

sig Partition{
	var leader: set Node
}


fun elems:Partition ->Node{
 	~ partition_id
}


abstract var sig Message {
	var from : one Node
}


var sig Preq,Presp,Creq,Lreq,LAreq,LAresp extends Message {}

var sig Cresp,Adv extends Message {
	var part_id: one Partition
}


/*************************************
 *          System Specification          *
 *************************************/



fact Message_config{
	-- always Message in Message' //keeps msg history
	always all m :Message | m in Message' => m.from'=m.from //keep the same source node for all states 
	always all m :Creq+Adv | m in Message' =>  m.part_id'=m.part_id
	--all m :Message |always m.from'=m.from // This condition implies that the entire Message set does not change over time.
}

//No exist duplicated messages.
fact Unique{ 
	always all disj a,b : Cresp  | a.from !=b.from or a.part_id != b.part_id
	always all disj a,b : Adv  | a.from !  =b.from or a.part_id != b.part_id
	always all disj a,b :Message- (Cresp + Adv ) |   a.from !=b.from 
}



/*
	In the initial state, there are no leaders, no partitions and no messages
	All nodes start without a partition
*/
fact Init
{
	no inbox
	no Message
	no partition_id
	no leader
	no (Node.role &Leader)
}

fact Common_configuration
{
	//in_Range is reflexive relation and does not contain the identity
	~in_range in in_range
	no (in_range & iden)
}

 

fact FTD_configuration 
{
	all n:FTD | n.role = REED
}



fact MTD_configuration {}



/*************************************
 *                 Transitions                *
 *************************************/

pred Nop{
	Message'=Message
	role'=role
	inbox'=inbox
	partition_id'=partition_id	
	leader'=leader
}

// Messages handling - Send messages
pred send[m:Message, nd_from:Node, nd_to:set Node,del_msg : set Message]{
	m.from'=nd_from
	Message'=(Message+ m) - del_msg
	
	nd_from.inbox'= nd_from.inbox - del_msg
	all n : nd_to | n.inbox'= n.inbox + m
	all n:Node-(nd_to+nd_from)| n.inbox'=n.inbox
}

// Messages handling - Delete messages
pred delete[m:set Message,nd_to:Node]{
	Message'=Message - m
	
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

	some m : Preq' | send[m,n,n.in_range,none] 

	role'=role
	partition_id'=partition_id	
	leader'=leader	
}


// 2- Router response for the candidate child. (Unicast)
pred send_ParentResponse [n :FTD] {
	
	some n.partition_id
	
	some m : Presp',  msg: (n.inbox & Preq)  | send[m,n,msg.from,msg] 

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
	--PC There is a Presp in the inbox 
	
	some m : Creq',  msg: (n.inbox & Presp)  | send[m,n,msg.from, msg] 
		

	role'=role
	partition_id'=partition_id	
	leader'=leader
}


// 4- The father accepts the son
pred send_ChildResponse [n :FTD] {
	
	--PC There is a Creq in the  inbox
	one n.partition_id
	some m : Cresp',  msg: (n.inbox & Creq)  | m.part_id'=n.partition_id and send[m,n,msg.from, msg] 
			
	role'=role
	partition_id'=partition_id	
	leader'=leader
}

----------

pred changed_to_leader[n:FTD]{
	--PC	
	no n.partition_id
	
	role '= role - (n->n.role) + (n->Leader)--becomes leader

	some p:Partition{
		no p.elems
		partition_id'=partition_id	+(n->p) - (n->n.partition_id)
		leader'=leader + (p->n)
	}
		
	inbox'=inbox
	Message'=Message
}


pred reset[n:Node]{
	n.role'=REED
	no n.inbox'
	no n.partition_id'
	all nd:Node -n |{
		nd.partition_id'=nd.partition_id
		nd.role'=nd.role
	}
	leader'= leader - (n.partition_id->n)
	delete[n.inbox,n] --clean my inbox
}




-- A Thread Device will always attach as an End Device
pred join_to_partition[n:Node]{
	 
	some msg: (n.inbox & Cresp) | {
		msg.from in n.in_range 
		partition_id'=partition_id	+ (n-> msg.part_id) -  (n->n.partition_id)
		delete[msg,n]
	}
	 
 	n in FTD => role'=role - (n->n.role) +(n->REED) 
		     else role'=role 
	leader'=leader - (Partition -> n) -- If the node is leader of any partition it ceases to be.	
}

/*
	Rules to merge:
		1.Se uma partição apenas tiver 1 elemento, esta cede e junta-se
		2. Weight Value maior  
		3. Partition ID Maior 
*/



--Multicast 
pred send_Advertisement[n:FTD]{
	n.role in (Leader +Router)
	some n.in_range
	some m : Adv' | m.part_id'= n.partition_id and  send[m,n,n.in_range,none] 
	
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

/*
	- Link Establishment Process Between Routers		

	   Link synchronization is performed in the following circumstances:
		- As part of the attachment process,
		- When a REED becomes an active Router.
		- When a Router receives a message from a neighboring device for which it does not
		   33 have a stored frame counter.
*/



-- Sent in multicast to all routers
pred send_LinkRequest[n:FTD]{
	n.role in REED
	one n.partition_id

	some m : Lreq' | send[m,n,(n.in_range & role.(REED + Router+Leader)),none] 

	role'=role
	partition_id'=partition_id	
	leader'=leader
}
--2 - Accept a link Request and Router request for the son to become part of your family 
pred send_LinkAcceptReq[n:FTD]{
	one n.partition_id
	some (n.inbox & Lreq) 

	some m : LAreq' ,  msg: (n.inbox & Lreq)  | send[m,n,msg.from, msg] 

	role'=role
	partition_id'=partition_id	
	leader'=leader
}

--3 - Positive Response  for the father
pred send_LinkAcceptResp[n:FTD]{
	one n.partition_id
	some (n.inbox & LAreq ) 

	some m : LAresp' ,  msg: (n.inbox & LAreq)  | send[m,n,msg.from,msg] 

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
	some in_range
} for  3 but exactly 1 FTD , 7 Message,exactly 2 Partition, 0 int, 8..13 steps
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



run {
	all n:Node| (Node-n) in n.^in_range
}  for exactly 2 Partition, 2 Node,exactly 2 FTD, 11 Message, 0 int , exactly 8 steps
/*
-- Tabelas - .
-- 10, 12, 14, steps
--  steps - 1  é nº de mensagens
-- varios solvers
--  5 runs 
 
*/
/*************************************
 *      Proprieties to be checked       *
 *************************************/
check lonePartition {
	always all n:Node | lone n.partition_id
}for   3 but  exactly  3 Partition,  8 Message, 0 int, 9 steps
//} //for  5 Node,exactly  3 Partition,  10 Message, 0 int, 1 steps

//run {} for  exactly  2 Node,exactly  3 Partition,  10 Message, 0 int, 1 steps
check  greedyLeader{
	always all p:Partition | lone p.leader  -- once  one n.partition_id => always some   n.partition_id

}for   3 but  exactly  3 Partition,  8 Message, 0 int, 9 steps


-- Liveness
check convergeToOnePartition{
 	fairness  and some FTD and  (all n:Node | (Node-n) in n.^in_range  and eventually always not reset[n]) =>  eventually  always (some p:Partition | Node in p.elems)  
} for   3 but exactly  3 Partition,  8 Message, 0 int, 9 steps


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
fun all_node_without_Partition : set Node  { 
	Node - partition_id.Partition
}

fun msg_in_inbox: set Message {
	Node.inbox
}

fun requests_in_inbox: set Message {
	Node.inbox :> (Preq + Creq+ Lreq + LAreq)
}

fun responses_in_inbox: set Message {
	Node.inbox :> (Presp + Cresp + LAresp)
} 




/*
fun fed : set Node  { 
	role.FED 
}

fun med : set Node  { 
	role.MED 
}
fun sed : set Node  { 
	role.SED 
}

fun router : set Node  { 
	role.Router
}

fun border_router : set Node  { 
	role.BorderRouter
}
fun th_leader:set Node{
	role.Leader
}

--network_of_partition
fun net : set Partition -> one ThreadNetwork{
	~partitions
}





/** Some links:
	- https://openthread.io/reference/group/api-thread-router#functions  -- Router/Leader header
**/

-- How to choose between leaders ?


import re
from utils.bcolors import bcolors as b
import json
import sys

FILENAME="examples/otns_0_cen6.replay"
json_file=None
#OTNS SPECS
RADIO_RANGE=160

node={}
last_ts={}

def preprocessFile(src_file):
    """ Removed unnecessary events 
        Tranformation doc to json    

    Args:
        src_file (str): filename of replay otns file

    Returns:
        json_file(dict): returns dict with json format 
    """
    with open (FILENAME, 'rt' ) as f:
        content = f.read()
        new0 = re.sub('.*(event:\{set_speed|event:\{set_network_info|event:\{set_node_rloc16|event:\{on_ext_addr_change|event:\{advance_time).*\n'  , r'', content, flags = re.M) # remove unnecessary events
        new1 = re.sub('(([a-z]|\_|[0-9])+):'  , r'"\1":', new0, flags = re.M) # add quotes to str before :
        new2 = re.sub(':([A-Za-z_]+)'  , r':"\1"', new1, flags = re.M)  # add quotes to strings after :
        new3 = re.sub(' '  , r', ', new2, flags = re.M)  #adding , in end of line
        new4 = re.sub('(.*)\n'  , r'{\1},\n', new3, flags = re.M)  #adding {} and , in the line
        new5 = re.sub('(.*)'  , r'[\1]', new4, flags = re.DOTALL)  #catch all file and put inside "{}" 
        new6 = re.sub(',\n\]\[\]$'  , r']', new5, flags = re.DOTALL)  #remove imprecision of latest cmd
        #print(new6)
        json_file = json.loads(new6)
        #print(f"{b.OKGREEN}Json tranformation complete.{b.ENDC}")
        f.close()
    return json_file


def getEvtName(json_str):
    name =  list(json_str["event"])[0]
    return name

def createhashTableForNodes(dict_processed, max_steps=-1):
    counter_paren=1 # count number of parenthesis needded
    processed_op=0 # count the number of events processed (because some events are ignored)
    count_changetoLeader=0 # serve to get number of exactly partitions of a run 
    to_print="" # was necessary because we need count the number of chars printed for delete the last ";" in the last operation.
    last_evt="" #save last event for otimization of move.
    print("run {")
    for op in dict_processed:
        evt=getEvtName(op)

        if evt=="add_node":
            processed_op+=1
            
            n1=op["event"]["add_node"]
            #print(op["event"]["add_node"]["node_id"])
            in_range = getNodesInrange(n1["node_id"],n1["x"],n1["y"]);
            node[n1["node_id"]]={"x":n1["x"],
                                 "y":n1["y"]};
            #print(f'addNode({n1["node_id"]},{in_range})')    
            if n1["node_id"]==1 :  # if is the first  :
                to_print=f'{ident(counter_paren)}some n{n1["node_id"]}:FTD\' {{ addNode[n{n1["node_id"]},{list_to_alloyMode(in_range)}];'
                print(to_print)            
            else:
                to_print=f'{ident(counter_paren)}some n{n1["node_id"]}:FTD\'-{put_parenthesis(gen_str_for_node(n1["node_id"]-1))} {{ addNode[n{n1["node_id"]},{list_to_alloyMode(in_range)}];'  
                print(to_print)            
            counter_paren+=1
            #print(f'addNode[n{n1["node_id"]},{list_to_alloyMode(in_range)}]')            
        elif evt=="set_node_pos":
            if last_evt=="set_node_pos":
                #delete last printed line
                #print("\33^[[2K\r")
                sys.stdout.write('\x1b[1A') # CURSOR_UP_ONE
                sys.stdout.write('\x1b[2K') #ERASE_LINE
                processed_op-=1 #remove one processed operation
            processed_op+=1
            n1=op["event"]["set_node_pos"]
            in_range = getNodesInrange(n1["node_id"],n1["x"],n1["y"]);
            node[n1["node_id"]]={"x":n1["x"],
                                 "y":n1["y"]};
            to_print=f'{ident(counter_paren)}move[n{n1["node_id"]},{list_to_alloyMode(in_range)}];'
            print(to_print)         
        elif evt=="send":
            msg=op["event"]["send"]
            list_msgs=getpossibleTransitions(msg)
            if list_msgs != []:
                processed_op+=1
                res=' or '.join(list_msgs)
                to_print=f'{ident(counter_paren)}{res};'
                print(to_print)
        #elif evt=="set_node_partition_id": # it is more abstract than the role 
        #    processed_op+=1
        #    n1=op["event"]["set_node_partition_id"]
        #    to_print=f'{ident(counter_paren)}changed_to_leader[n{n1["node_id"]} or join_to_partition[n{n1["node_id"]} or merge_partitions[n{n1["node_id"]}];'
        #    print(to_print)
        elif evt=="set_node_role":#ignoring Router and detached roles
            n1=op["event"]["set_node_role"]
            if n1["role"]=="OT_DEVICE_ROLE_CHILD":
                processed_op+=1
                to_print=f'{ident(counter_paren)}join_to_partition[n{n1["node_id"]}] or merge_partitions[n{n1["node_id"]}];'
                print(to_print)
            elif n1["role"]=="OT_DEVICE_ROLE_LEADER":
                count_changetoLeader+=1
                processed_op+=1
                to_print=f'{ident(counter_paren)}change_to_leader[n{n1["node_id"]}];'
                print(to_print)
            elif n1["role"]=="OT_DEVICE_ROLE_ROUTER":
                processed_op+=1
                to_print=f'{ident(counter_paren)}change_to_router[n{n1["node_id"]}];'
                print(to_print)
        #else:
            #just for help in debug
            #print(f'\t{b.WARNING}{op["event"][evt]} {b.ENDC}' )
        if processed_op==max_steps:
            break
        last_evt=evt 
    last_paren = '}'* (counter_paren)
    sys.stdout.write(f"\033[F\033[{len(to_print)}G \n")#move 12 char to last line
    if  count_changetoLeader >= 0:
        print(f'{last_paren}  for {counter_paren-1} but exactly {count_changetoLeader} Partition, {processed_op+1}..{processed_op+1} steps')
    else:
        print(f'{last_paren}  for {counter_paren-1} but {processed_op+1}..{processed_op+1} steps')

def checknodesInSameRange(n1_x,n1_y,n2_x,n2_y,radius_range):
    """Check if two nodes are in same range

    Args:
        n1_x (int): coordinate x of node 1
        n1_y (int): coordinate y of node 1
        n2_x (int): coordinate x of node 2
        n2_y (int): coordinate y of node 2
        radius_range (int): radius 

    Returns:
        Boolean: True if they are in the same range
    """
    x_flag=False
    y_flag=False

    if n2_x >= (n1_x -radius_range) and n2_x <= (n1_x +radius_range): 
        #está dentro
        x_flag=True
    if  n2_y >= (n1_y -radius_range) and n2_y <= (n1_y +radius_range): 
        y_flag=True
    return (x_flag and y_flag)
    
    
def getNodesInrange(id,x,y):
    in_range=[]
    for n in node.keys():
        if (n != id and checknodesInSameRange(x,y,node[n]["x"], node[n]["y"], RADIO_RANGE )):
            in_range.append(n)
    return in_range    

def getpossibleTransitions(msg={}):
    src_id=msg["src_id"]
    if "dst_id" in msg:
        dst_id=msg["dst_id"]
    else:
        dst_id=-1
    frame_control=msg["mv_info"]["frame_control"]
    if dst_id == -1 and frame_control== 55361 :
        return [f"send_ParentRequest[n{src_id}]",f"send_Advertisement[n{src_id}]"]
    elif dst_id != -1 and frame_control== 56417:
        return [f"send_ParentResponse[n{src_id}]", f"send_ChildRequest[n{src_id}]"]
    elif dst_id != -1 and frame_control== 56441:# or 56425
        return [f"send_ChildResponse[n{src_id}]"]
    elif dst_id != -1 and frame_control== 39017:
        return [f"send_LinkReq[n{src_id},n{dst_id}]",f"send_LinkResp[n{src_id},n{dst_id}]", f"send_LinkAcceptReq[n{src_id}]",f"send_LinkAcceptResp[n{src_id}]"]
    elif dst_id == -1 and frame_control== 39017:
        return [f"send_LinkRequest[n{src_id}]"]
    else :
        #print(f'{b.WARNING}\tNEW-MSG-FOUND->(src: {src_id}, dst: {dst_id}, frame_control: {frame_control} ){b.ENDC}')#seq: {msg["mv_info"]["seq"]}){b.ENDC}')
        return []
        #return [f'{b.WARNING}\tNEW-MSG-FOUND->(src: {src_id}, dst: {dst_id}, frame_control: {frame_control}, seq: {msg["mv_info"]["seq"]}){b.ENDC}' ]
    
    
def gen_str_for_node(n,depth=0,seperator='+'):
    if n==0:
        return ''
    res=''  
    while(n>depth):
        if (n==depth+1):
            res += f'n{n}'
        else:
            res += f'n{n}{seperator}'
        n-=1
    #print(res)
    return res
    

def list_to_alloyMode(l=[]):
    if l==[]:
        return "none"
    else:
        res=''
        i=0
        while (i<len(l)):
            if i==0:
                res += f'n{l[i]}'
            else :
                res += f'+n{l[i]}'
            i+=1
        
        return res 
            
def put_parenthesis(input):
    op_to_check = ['+', '-']
    if any(op in input for op in op_to_check):
        return f'({input})'
    return input
    
    
def ident(number=0):
    return "  " *number
        
if __name__ == "__main__":
    #print(f"{b.OKCYAN}Welcome to Parser - From Otns replay to Alloy{b.ENDC}")
    num=-1
    try:
        if (len(sys.argv) ==2 ):
            num=int(sys.argv[1])
            if num <=0 :
                print(f'{b.FAIL}The number of steps should be positive!{b.ENDC}') 
                exit()
    except ValueError:
        print(f"{b.FAIL}That's not an integer. Try again!{b.ENDC}")
        exit()
    json_file = preprocessFile(FILENAME)
    createhashTableForNodes(json_file,num)
    #gen_str_for_node(5,0)
    #print(put_parenthesis("n1"))
    #print(put_parenthesis("n1+n2"))
    #print(list_to_alloyMode([3,2,1]))
    
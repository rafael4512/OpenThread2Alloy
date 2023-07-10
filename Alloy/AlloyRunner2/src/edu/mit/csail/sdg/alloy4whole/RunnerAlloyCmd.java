package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import java.util.concurrent.Callable;

public class RunnerAlloyCmd implements Callable<A4Solution> {

    private final A4Reporter a ;
    private final CompModule cm ;
    private final Command cmd ;
    private final A4Options opt;

    public RunnerAlloyCmd(A4Reporter a ,CompModule cm ,Command cmd , A4Options opt ) {
        this.a = a;
        this.cm=cm;
        this.cmd=cmd;
        this.opt=opt;
    }
    public A4Solution call() throws Exception {
        //Run Alloy command;
        try {
            A4Solution ans = TranslateAlloyToKodkod.execute_command(a, cm.getAllReachableSigs(), cmd, opt);

            return ans;
        }catch (Exception e){
            //System.out.println(e);
        }
        return null;
    }
}

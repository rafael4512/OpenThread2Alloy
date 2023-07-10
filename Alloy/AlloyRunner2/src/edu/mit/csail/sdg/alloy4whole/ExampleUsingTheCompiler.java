/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4whole;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.concurrent.*;

/** This class demonstrates how to access Alloy4 via the compiler methods. */


public final class ExampleUsingTheCompiler {

    /*
     * Execute every command in every file.
     *
     * This method parses every file, then execute every command.
     *
     * If there are syntax or type errors, it may throw
     * a ErrorSyntax or ErrorType or ErrorAPI or ErrorFatal exception.
     * You should catch them and display them,
     * and they may contain filename/line/column information.
     */

    //Executa  36 commandos por ficheiro= 108 commandos;
    //27 horas no pior caso. Todos darem timeout.

    public void beep(int numberOfBeeps){
        for (int i = 0; i < numberOfBeeps; ++i) {

            // Ring the bell again using the Toolkit
            java.awt.Toolkit.getDefaultToolkit().beep();
            try {
                Thread.sleep(1000); // introduce delay
            } catch (InterruptedException e) {
            }
        }
    }
    public SendMessage telegramBot =new SendMessage();

    public static void main(String[] args) throws Err, FileNotFoundException {

        ExampleUsingTheCompiler e =new ExampleUsingTheCompiler();
        SendMessage telegramBot =new SendMessage();
        e.runAlloy();
        //e.beep(3);
    }

    public  void runAlloy() throws Err, FileNotFoundException {

        //RUn on maximum time of 15 min .- https://stackoverflow.com/questions/1164301/how-do-i-call-some-blocking-method-with-a-timeout-in-java

        String curr_dir =System.getProperty("user.dir");
        System.out.println(System.getProperty("os.name"));
        String file1, file2,file3,file4,file5,file6,file7,file8,file9,file10,file11,file12=null;
        if (System.getProperty("os.name").startsWith("Windows")){
             file1= curr_dir +"\\..\\Models\\m4_OtnsCompatible.als";
             file2= curr_dir +"\\..\\Models\\m2_DynamicMsg.als";
             file3= curr_dir +"\\..\\Models\\m3_ExplicitMsg.als";
        }else {
             file1= curr_dir +"/../Models/m4_OtnsCompatible.als";
             file2= curr_dir +"/../Models/m2_DynamicMsg.als";
             file3= curr_dir +"/../Models/m3_ExplicitMsg.als";
        }
        //Output directory
        String testsDirectory="../tests/";
        String outputFileName= testsDirectory + "Output.txt";


        String[] all_filenames = new String[]{file1};
        System.out.println();
        telegramBot.sendToTelegram("Mac program - Started!\nFilename:"+outputFileName);

        // Alloy4 sends diagnostic messages and progress reports to the A4Reporter.
        // By default, the A4Reporter ignores all these events (but you can extend the A4Reporter to display the event for the user)
        A4Reporter rep = new A4Reporter() {
            // For example, here we choose to display each "warning" by printing it to System.out
            @Override
            public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
                System.out.flush();
            }
        };


        try {


            PrintStream o = new PrintStream(new File(outputFileName));
            PrintStream console = System.out;// Store current System.out, before assigning a new value
            System.setOut(o);

            // The visualizer (We will initialize it to nonnull when we visualize an Alloy solution)
            VizGUI viz = null;

            // Print the Time before Running
            SimpleDateFormat formatter = new SimpleDateFormat("yyyy-MM-dd 'at' HH:mm:ss z");
            Date date = new Date(System.currentTimeMillis());
            System.out.println("Começou a executar :" + formatter.format(date));

            int ite=0, n_cmd=0;
            //A4Options.SatSolver.ElectrodX - testar para 3 no scope . ( Unbounded - 1.. steps)
            A4Options.SatSolver[] solvers = { A4Options.SatSolver.MiniSatJNI, A4Options.SatSolver.GlucoseJNI, A4Options.SatSolver.SAT4J, A4Options.SatSolver.LingelingJNI};
            //A4Options.SatSolver[] solvers = { A4Options.SatSolver.ElectrodS};
            //A4Options.SatSolver[] solvers = {A4Options.SatSolver.ElectrodX};

            for (String filename : all_filenames) {
                System.out.println("\n\n**************\nFILENAME : " + filename + "\n**************\n");
                for (A4Options.SatSolver sol : solvers) {
                    for (int i = 0; i < 1; i++) { // Decompose Strategy (0=Off 1=Hybrid 2=Parallel) JUST BATCH

                        // Parse+typecheck the model
                        System.out.println("=========== Parsing+Typechecking " + filename + " =============");
                        CompModule world = CompUtil.parseEverything_fromFile(rep, null, filename);

                        // Choose some default options for how you want to execute the commands
                        A4Options options = new A4Options();
                        options.solver = sol;
                        options.decompose_mode = i;
                        for (Command command : world.getAllCommands()) {
                            // Execute the command
                            System.out.println("============ Command " + command + ": ============");

                                //create callable
                                ExecutorService executor = Executors.newCachedThreadPool();
                                Callable<A4Solution> task = new RunnerAlloyCmd(rep, world, command, options);
                                Future<A4Solution> future = executor.submit(task);
                                long startTime = System.nanoTime();


                                // get Output of Callable object;
                                try {

                                    A4Solution ans = future.get(15, TimeUnit.MINUTES); //15 min no maximo por commando.
                                    // Print the outcome
                                    if (ans != null) {
                                        if (ans.satisfiable())
                                            System.out.println("SAT");
                                        else
                                            System.out.println("UNSAT");
                                    }else {
                                        System.out.println("Null returned, has not been executed");

                                        //entra aqui 2 vezes por cada ficheiro - LingelingJNI, hybrid
                                        // Nos comandos = Command Check convergeToOnePartition for 3 but 0 int 9 steps, exactly 3 Partition, 8 Message:
                                        //                        Check greedyLeader for 3 but 0 int 9 steps, exactly 3 Partition, 8 Message:

                                    }
                                } catch (TimeoutException ex) {
                                    System.out.println("Timeout");
                                    // handle the timeout
                                } catch (InterruptedException e) {
                                    // handle the interrupts
                                    System.out.println("InterruptedExecption\n" + e.toString());
                                } catch (ExecutionException e) {
                                    // handle other exceptions
                                    System.out.println("ExecutionException\n" + e.toString());
                                } finally {
                                    future.cancel(true); // may or may not desire this
                                    //System.out.println("Finally");
                                    long stopTime = System.nanoTime();
                                    long elapsedTime = (stopTime - startTime);
                                    ++n_cmd;
                                    if (n_cmd ==2*5){
                                        //30% concluido
                                        telegramBot.sendToTelegram("Mac program - 30% concluded (20/60) ");
                                    } else if (n_cmd==4*5) {
                                        //60% concluido
                                        telegramBot.sendToTelegram("Mac program - 60% concluded (40/60) ");
                                    } else if (n_cmd==6*5) {
                                        //90% concluido
                                        telegramBot.sendToTelegram("Mac program - 90% concluded (50/60) ");
                                    }

                                    System.out.println("TestNumber = " + n_cmd); //number of test
                                    System.out.println("Steps = " + command.maxprefix); // number of steps - create set function.
                                    System.out.println("Solver = " + sol.toString()); //Solver
                                    System.out.println("Decomposer strategy = " + (i == 0 ? "batch": "")  + (i==1?  "hybrid":"")+ (i==2?  "Parallel":"")); //Strategy
                                    System.out.println("Elapsed Time : " + ((double) TimeUnit.MILLISECONDS.convert(elapsedTime, TimeUnit.NANOSECONDS) / 1000));


                                }


                                // If satisfiable...
                            /*if (ans.satisfiable()) {
                                // You can query "ans" to find out the values of each set or type.
                                // This can be useful for debugging.
                                //
                                // You can also write the outcome to an XML file
                                ans.writeXML("alloy_example_output.xml");
                                //
                                // You can then visualize the XML file by calling this:
                                if (viz == null) {
                                    viz = new VizGUI(false, "alloy_example_output.xml", null);
                                } else {
                                    viz.loadXML("alloy_example_output.xml", true);
                                }
                            }*/


                        }

                    }
                }

            }
            Date date2 = new Date(System.currentTimeMillis());
            System.out.println("\n\n\nAcabou de executar :" + formatter.format(date2));
            System.setOut(console); // print to terminal
            System.out.println("\n\n#######\n#######\nACABOU DE CORRER\n#######\n#######\n");
            telegramBot.sendToTelegram("Mac program - Finished!");
            System.exit(0);
        } catch (Exception e) { }
    }
}
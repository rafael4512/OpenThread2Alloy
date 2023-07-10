
# AlloyRunner2

#### Description 

Este programa java permite executar vários comandos do Alloy sem interação com a interface.
Para alem disso, foi criado um bot do telegram para saber quando os testes eram concluidos, dado que alguns poderiam demorar várias horas.


____


#### Usage:

If you run on IDE,such as IntelliJ, Netbeans or eclipse, go to the file "ExampleUsingTheCompiler": 

First you have to specify which file you want to run in the variables called `file1,file2,...`(line 88..95) and you can run several files. Then you choose the solvers in the variable `solvers`(line 135). Afterwards, just run the main.


If you want to run on a server (e.g. AWS EC2), use:  

```
java -Dfile.encoding=UTF-8 -classpath /home/ec2-user/OpenThread2Alloy/Alloy/AlloyRunner2/out/production/AlloyRunner2:/home/ec2-user/OpenThread2Alloy/Alloy/AlloyRunner2/dist/lib/org.alloytools.alloy.dist.jar edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler
```

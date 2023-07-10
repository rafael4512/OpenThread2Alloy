
# Parser

#### Description 

The parser is a program written in Python, which allows the creation of instances for Alloy through the output of the OpenThread Network Simulator.
This is accomplished using Regex and a Hash table as the data structure.

____

#### Usage:

To run this program, just use the following command:
```
python3 otns2alloy [STEPS]
```
`STEPS` - is an optional parameter that allows to limit the number of steps of a generated snapshot, due to the limitations of Alloy.

By default, the program uses an example that is in the examples folder, but this can be changed. The `FILENAME` variable defines the target file of the OTNS output. This can be found on line 6 of the otns2alloy file.
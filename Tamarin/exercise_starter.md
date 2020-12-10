# Starter exercise

Extract the files in the file `tamarin_ex1_part1.zip`

## Question 1

Consider `NAXOS_01_simple.spthy`

The exercise involves modifying the inputs to the `h2` function: this is the key-derivation function of the protocol that combines several elements. The idea is to modify the input file to remove a single input to the function, and analysing the results. Note that any changes should be done both on the initiator and responder side.

  * Q1.1: Remove the first input to `h2` on both roles and analyse the resulting protocol. 
     * What happens to the properties? Can you explain why?
  * Q1.2: Restore the original file, and now remove the second input, and analyse again. Repeat for all inputs.
i
## Question 2

Consider `NAXOS_08_eCK.spthy`. This is a similar input file to the previous, but it has a more complicated threat model, encoded in the stronger security property. 

Go through the same steps as for Question 1.  Compare the results to before. Why do they differ?

## Question 3

Compare `NAXOS_08_eCK.spthy` and `NAXOS_15_eCK_FPS.spthy`.
Explain the difference, possibly by referring to different analysis results and the difference in the input files.

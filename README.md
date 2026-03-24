# Assignment I: The IMP language in Isabelle

This is the first of two marked assignments for the course "Proof Assistants"
(L81), covering the Isabelle part of the course.  This assignment comprises
a number of small formalisation and verification tasks related to the imperative
programming language IMP, as well as a short write-up explaining your work.
See the course website for details on the assessment.

Please use the template theory file `Assignment1.thy` to work on the tasks.
The remaining theory files in this folder are copies of theories defining the
IMP language.

The ROOT file and the LaTeX files in the `document` folder are set up for
document generation:  running `isabelle build -D .` should produce a file
`document.pdf` in the `output` folder that includes the contents of
`Assignment1.thy`, as well as a variant of that without proofs in
`assignment1.pdf` (that is the handout file on the website).

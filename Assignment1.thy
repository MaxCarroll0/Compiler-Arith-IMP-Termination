(*<*)
theory Assignment1
  imports Big_Step
begin
(*>*)

text \<open>The following tasks are about writing/generaMting and verifying programs in the IMP language.

  Note that the version of the IMP language defined in the files in this assignment template uses
  natural numbers as variable identifiers rather than strings, in order to simplify reasoning about
  variable names.\<close>

(*-------------------------------------------------------------------------------------------*)

text_raw \<open>\BeginTask{4 marks}\<close>

text \<open>Prove the following lemma about the preservation of invariants, which can be useful when
  proving properties about programs containing WHILE loops:\<close>

lemma While_inv:
  assumes loop: "(WHILE b DO c, s) \<Rightarrow> t"
    and preservation: "\<And>s t. (c, s) \<Rightarrow> t \<Longrightarrow> bval b s \<Longrightarrow> Inv s \<Longrightarrow> Inv t"
    and start: "Inv s"
  shows "\<not>bval b t \<and> Inv t"
proof-
  from loop start show ?thesis
  by (induction "WHILE b DO c"  s t rule: big_step_induct) (auto simp: start preservation)
qed

text_raw \<open>\EndTask\<close>

(*-------------------------------------------------------------------------------------------*)

text_raw \<open>\BeginTask{15 marks}\<close>

text \<open>The basic arithmetic expression language @{typ aexp} in our IMP language only supports
  addition, but we can still write programs that perform other arithmetic operations.

  Write a program that subtracts the value of variable 1 from the value of variable 0 and stores
  the result in variable 2:\<close>

definition eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "eq a b \<equiv> And (Not (Less a b)) (Not (Less b a))"

definition minus_com :: com where
  "minus_com \<equiv> 2 ::= V 0;;
               (WHILE Not (eq (V 0) (Plus (V 1) (V 2))) DO 
                 (IF Less (V 1) (N 0)
                  THEN 2 ::= Plus (V 2) (N 1)
                  ELSE 2 ::= Plus (V 2) (N (-1))))"

text \<open>You may use all commands of the IMP language including WHILE and IF commands,
  as well as additional variables.\<close>

text \<open>Prove your program correct:\<close>


lemma
  "(minus_com, s) \<Rightarrow> t  \<Longrightarrow>  t 2 = s 0 - s 1"
proof -
  assume "(minus_com, s) \<Rightarrow> t"

  then obtain init loop b c r where
    "minus_com = init;; loop" and 
    init_def: "init = 2 ::= V 0" and
    loop_def: "loop = WHILE b DO c" and
    b_def: "b = Not (eq (V 0) (Plus (V 1) (V 2)))" and
    c_def: "c = IF Less (V 1) (N 0)
                THEN 2 ::= Plus (V 2) (N 1)
                ELSE 2 ::= Plus (V 2) (N (-1))" and
    init_eval: "(init, s) \<Rightarrow> r" and
    loop_eval: "(loop, r) \<Rightarrow> t"
    unfolding minus_com_def by blast

  let ?Inv = "\<lambda>s'. s' 0 = s 0 \<and> s' 1 = s 1"

  have "(WHILE b DO c, r) \<Rightarrow> t" using loop_eval loop_def by simp
  then have "\<not>bval b t \<and> ?Inv t" 
    proof (rule While_inv[of b c r t ?Inv])
      show start: "?Inv r" using init_eval init_def by auto
      show preservation: "\<And>s' t'. (c, s') \<Rightarrow> t' \<Longrightarrow> bval b s' \<Longrightarrow> ?Inv s' \<Longrightarrow> ?Inv t'" 
        using c_def by auto
    qed

  then show "t 2 = s 0 - s 1" using b_def unfolding eq_def by simp
qed

text_raw \<open>\EndTask\<close>

(*-------------------------------------------------------------------------------------------*)

text_raw \<open>\BeginTask{3 marks}\<close>

text \<open>Now consider the following expression language that extends @{typ aexp} with subtraction and
  multiplication:\<close>

datatype aexp2 =
    N2 int
  | V2 vname
  | Plus2 aexp2 aexp2
  | Minus2 aexp2 aexp2
  | Mult2 aexp2 aexp2

text \<open>Write an evaluation function and a function determining the variables appearing in an
  expression:\<close>

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> int" where
"aval2 (N2 n) s = n" |
"aval2 (V2 v) s = s v" |
"aval2 (Plus2 a1 a2) s = (aval2 a1 s) + (aval2 a2 s)" |
"aval2 (Minus2 a1 a2) s = (aval2 a1 s) - (aval2 a2 s)" |
"aval2 (Mult2 a1 a2) s = (aval2 a1 s) * (aval2 a2 s)"

fun avars2 :: "aexp2 \<Rightarrow> vname set" where
"avars2 (N2 n) = {}" |
"avars2 (V2 v) = {v}" |
"avars2 (Plus2 a1 a2) = avars2 a1 \<union> avars2 a2" |
"avars2 (Minus2 a1 a2) = avars2 a1 \<union> avars2 a2" |
"avars2 (Mult2 a1 a2) = avars2 a1 \<union> avars2 a2"

text \<open>Show the following congruence lemma, stating that evaluating an @{typ aexp2} expression in
  two states agreeing on the values of variables appearing in the expression gives the same result,
  i.e. the value of an expression does not depend on variables that don't appear in it:\<close>

lemma aval2_cong:
  "(\<forall>v. v \<in> avars2 e \<longrightarrow> s v = t v)  \<Longrightarrow>  aval2 e s = aval2 e t"
  by (induction e rule: aexp2.induct) auto

text_raw \<open>\EndTask\<close>

(*-------------------------------------------------------------------------------------------*)

text_raw \<open>\BeginTask{10 marks}\<close>

text \<open>Write a compiler \<open>com_of_aexp2\<close> from an @{typ aexp2} expression to a program
  in the original IMP language (possibly using loops and conditionals for evaluating
  sub-expressions not supported there, as well as additional variables for intermediate values),
  where the program \<open>com_of_aexp2 res e\<close> writes the result of evaluating \<open>e\<close> to variable \<open>res\<close>:\<close>

text "Calling Convention:
      Arguments in register 0 by register 1. And these are always preserved.
      Result in register 2. 
      Register 3 is temporary and corruptible.
      Register 4 is also corruptible in mult_com.
      Registers 5, 6 are corruptible in the full compiler.

      Note that my original minus implementation adheres to this convention.

      mult_com_pos terminates correctly only for positive multipliers in reg 0, but always terminates.
      mult_com uses minus_pos_com with unary_minus_com to extend to negative multipliers
      where unary minus inverts the value in register 0 (and stores it in register 2)."

definition mult_pos_com :: com where
  "mult_pos_com \<equiv> 2 ::= N 0;;
                   3 ::= N 0;;
                   (WHILE Less (V 3) (V 0) DO (
                     2 ::= Plus (V 2) (V 1);;
                     3 ::= Plus (V 3) (N 1)
                    ))"

definition unary_minus_com :: com where
  "unary_minus_com \<equiv> 3 ::= V 1;;
                      1 ::= V 0;;
                      0 ::= N 0;;
                      minus_com;;
                      0 ::= V 1;;
                      1 ::= V 3"

definition mult_com :: com where
  "mult_com \<equiv> IF Less (V 0) (N 0)
               THEN (unary_minus_com;;
                    0 ::= V 2;;
                    mult_pos_com;;
                    4 ::= V 2;;
                    unary_minus_com;;
                    0 ::= V 4;;
                    4 ::= V 2;;
                    unary_minus_com;;
                    0 ::= V 4)
               ELSE mult_pos_com"

fun com_of_aexp2 :: "vname \<Rightarrow> aexp2 \<Rightarrow> com" where
"com_of_aexp2 res (N2 n)         = res ::= (N n)" |
"com_of_aexp2 res (V2 v)         = res ::= (V v)" |
"com_of_aexp2 res (Plus2 a1 a2)  = com_of_aexp2 res a1;;
                                   com_of_aexp2 (res + 1) a2;;
                                   res ::= Plus (V res) (V (res + 1))" |
"com_of_aexp2 res (Minus2 a1 a2) = com_of_aexp2 res a1;;
                                   com_of_aexp2 (res + 1) a2;;
                                   0 ::= V res;;
                                   1 ::= V (res + 1);;
                                   minus_com;;
                                   res ::= V 2" |
"com_of_aexp2 res (Mult2 a1 a2)  = com_of_aexp2 res a1;;
                                   com_of_aexp2 (res + 1) a2;; 
                                   0 ::= V res;;
                                   1 ::= V (res + 1);;
                                   mult_com;;
                                   res ::= V 2"

text \<open>Test your compiler using some example expressions.

  Explain informally in your write-up how, why, and under what conditions the compiler works.

  Treating registers 2 and 3 as corruptible. With 2 being the result register (for minus and mult).
  Registers 0 and 1 are argument registers to minus and mult, but are preserved.
  This formulation fits with the previous minus_com and also a new mult.
  mult_com requires corruptible temporary register 3 to ensure preservation of argument registers 0 and 1.\<close>

value "com_of_aexp2 0 (Plus2 (Minus2 (V2 0) (V2 1)) (V2 5))"

text "TODO: update examples. Valid expressions checking 0 has correct result and that r > 5 are preserved, 
      but 2,3,4 are corrupted.
      Tested to 3 levels down"

values "{map t [0,1,2,3,4,5] |t. 
          (com_of_aexp2 0 (Plus2 (Minus2 (V2 5) (V2 6)) (V2 7)), 
          <0 := 2, 1 := 1, 2 := 99, 3 := 98, 4 := 97, 5 := 1, 6 := 5>) 
        \<Rightarrow> t}"

values "{map t [0,1,2,3,4,5] |t. 
          (com_of_aexp2 0 (Minus2 (Minus2 (V2 0) (V2 1)) (V2 5)), 
          <0 := 2, 1 := 1, 2 := 99, 3 := 98, 4 := 97, 5 := 1>) 
        \<Rightarrow> t}"

values "{map t [0,1,2,3,4,5] |t. 
          (com_of_aexp2 0 (Minus2 (Minus2 (Minus2 (V2 0) (V2 1)) (Minus2 (V2 0) (V2 6))) (V2 5)), 
          <0 := 3, 1 := 1, 2 := 99, 3 := 98, 4 := 97, 5 := 2, 6 := 4>) 
        \<Rightarrow> t}"

values "{map t [0,1,2,3,4,5] |t. 
          (com_of_aexp2 0 (Mult2 (Minus2 (V2 0) (V2 1)) (V2 5)), 
          <0 := 3, 1 := 1, 2 := 99, 3 := 98, 4 := 97, 5 := 2>) 
        \<Rightarrow> t}"

text "Invalid expressions making use of register 1 produces wrong result"

values "{map t [0,1,2,3,4,5] |t. 
          (com_of_aexp2 0 (Mult2 (Minus2 (V2 2) (V2 1)) (V2 5)), 
          <0 := 3, 1 := 1, 2 := 99, 3 := 98, 4 := 97, 5 := 2>) 
        \<Rightarrow> t}"

text "Valid expressions correctly stores result to corruptible register 1"

values "{map t [0,1,2,3,4,5] |t. 
          (com_of_aexp2 1 (Mult2 (Minus2 (V2 0) (V2 1)) (V2 5)), 
          <0 := 3, 1 := 1, 2 := 99, 3 := 98, 4 := 97, 5 := 2>) 
        \<Rightarrow> t}"

text_raw \<open>\EndTask\<close>

(*-------------------------------------------------------------------------------------------*)

text_raw \<open>\BeginTask{18 marks}\<close>

text \<open>Prove (partial) correctness of the programs generated by @{term com_of_aexp2}.  You may add
  assumptions to the lemma capturing the conditions under which your compiler works, as explained
  above.\<close>

lemma minus_partial: 
  assumes "(minus_com, s) \<Rightarrow> t"
  and corrupt2: "r \<noteq> 2"
  shows "t 2 = s 0 - s 1 \<and> t r = s r"
proof-
  from assms obtain init loop b c ss where
    "minus_com = init;; loop" and 
    init_def: "init = 2 ::= V 0" and
    loop_def: "loop = WHILE b DO c" and
    b_def: "b = Not (eq (V 0) (Plus (V 1) (V 2)))" and
    c_def: "c = IF Less (V 1) (N 0)
                THEN 2 ::= Plus (V 2) (N 1)
                ELSE 2 ::= Plus (V 2) (N (-1))" and
    init_eval: "(init, s) \<Rightarrow> ss" and
    loop_eval: "(loop, ss) \<Rightarrow> t"
    unfolding minus_com_def by blast

  let ?Inv = "\<lambda>s'. s' r = s r \<and> s' 0 = s 0 \<and> s' 1 = s 1"

  have "(WHILE b DO c, ss) \<Rightarrow> t" using loop_eval loop_def by simp
  then have "\<not>bval b t \<and> ?Inv t"
    proof (rule While_inv[of b c ss t ?Inv])
      show start: "?Inv ss" using init_eval init_def corrupt2 by auto
      show preservation: "\<And>s' t'. (c, s') \<Rightarrow> t' \<Longrightarrow> bval b s' \<Longrightarrow> ?Inv s' \<Longrightarrow> ?Inv t'" 
        using c_def assms(2) by auto
    qed
  then show "?thesis" using b_def unfolding eq_def by auto
qed

lemma
  mult_pos_partial: 
  assumes "(mult_pos_com, s) \<Rightarrow> t" 
  and pos: "s 0 \<ge> 0"
  and corrupt2: "r \<noteq> 2"
  and corrupt3: "r \<noteq> 3"
  shows "t 2 = s 0 * s 1 \<and> t r = s r"
proof-
  from assms
  obtain init loop b c ss where
    "mult_pos_com = init;; loop" and 
    init_def: "init = 2 ::= N 0;;
                      3 ::= N 0" and
    loop_def: "loop = WHILE b DO c" and
    b_def: "b = Less (V 3) (V 0)" and
    c_def: "c = 2 ::= Plus (V 2) (V 1);;
                     3 ::= Plus (V 3) (N 1)" and
    init_eval: "(init, s) \<Rightarrow> ss" and
    loop_eval: "(loop, ss) \<Rightarrow> t"
    unfolding mult_pos_com_def by blast

  let ?Frame = "\<lambda>s'. s' 0 = s 0 \<and> s' 1 = s 1 \<and> s' r = s r"
  let ?Inv = "\<lambda>s'. s' 3 \<le> s 0 \<and> (s' 2 = s' 3 * s 1) \<and> ?Frame s'"

  have "(WHILE b DO c, ss) \<Rightarrow> t" using loop_eval loop_def by simp
  then have "\<not>bval b t \<and> ?Inv t" 
    proof (rule While_inv[of b c ss t ?Inv])
      show start: "?Inv ss" using init_eval init_def corrupt2 corrupt3 pos by auto
      show preservation: "\<And>s' t'. (c, s') \<Rightarrow> t' \<Longrightarrow> bval b s' \<Longrightarrow> ?Inv s' \<Longrightarrow> ?Inv t'" 
        using c_def corrupt2 corrupt3 b_def by (auto simp: algebra_simps)
    qed

  then show "?thesis" using b_def by auto
qed

lemma unary_minus_partial: 
  assumes "(unary_minus_com, s) \<Rightarrow> t"
  and "r \<noteq> 2" and "r \<noteq> 3" 
  shows "t 2 = - s 0 \<and> t r = s r"
using assms unfolding unary_minus_com_def by (auto simp: minus_partial)

lemma mult_partial: 
  assumes "(mult_com, s) \<Rightarrow> t"
  and "r \<noteq> 2" and "r \<noteq> 3" and "r \<noteq> 4" 
  shows "t 2 = s 1 * s 0 \<and> t r = s r"
using assms unfolding mult_com_def by (auto simp: unary_minus_partial mult_pos_partial)

lemma com_of_aexp2_correct:
  assumes "(com_of_aexp2 res e, s) \<Rightarrow> t"
  and "res > 4"
  and "\<forall>r. r \<in> avars2 e \<longrightarrow> r > 4 \<and> r < res"
  and "r > 4" and "r < res"
  shows "t res = aval2 e s \<and> t r = s r"
using assms proof (induction res e arbitrary: s t r rule: com_of_aexp2.induct)
  case (3 res a1 a2)
  note ctx = this
  from ctx obtain s' t' where 
    rec_call1: "(com_of_aexp2 res a1, s) \<Rightarrow> s'" and
    rec_call2: "(com_of_aexp2 (res + 1) a2, s') \<Rightarrow> t'" and 
    fin: "(res ::= Plus (V res) (V (res + 1)), t') \<Rightarrow> t" by auto

  have obvious: "\<forall>r. r \<in> avars2 a2 \<longrightarrow> r < res + 1" using ctx(5) by auto
  then have a: "s' r = s r \<and> t' r = s' r" using rec_call1 rec_call2 ctx by simp
  then have frame: "t r = s r" using fin ctx by auto
  have preserve_res: "t' res = s' res" using obvious rec_call2 ctx by auto

  have "\<forall>r. r \<in> avars2 a2 \<longrightarrow> s' r = s r" using rec_call1 ctx by simp
  then have "t' res = aval2 a1 s \<and> t' (res + 1) = aval2 a2 s" 
    using aval2_cong[of a2 s' s] obvious preserve_res rec_call1 rec_call2 ctx by auto
  then have "t res = aval2 (Plus2 a1 a2) s" using fin  by auto
  
  then show ?case using frame by auto
next
  case (4 res a1 a2)
  note ctx = this
  from ctx obtain s' t' t2 t3 where 
    rec_call1: "(com_of_aexp2 res a1, s) \<Rightarrow> s'" and
    rec_call2: "(com_of_aexp2 (res + 1) a2, s') \<Rightarrow> t'" and
    prefin: "(0 ::= V res;; 1 ::= V (res + 1), t') \<Rightarrow> t2" and
    minus: "(minus_com, t2) \<Rightarrow> t3" and 
    fin: "(res ::= V 2, t3) \<Rightarrow> t" 
    by (smt (verit, ccfv_threshold) Seq SeqE com_of_aexp2.simps(4))

  have obvious: "\<forall>r. r \<in> avars2 a2 \<longrightarrow> r < res + 1" using ctx(5) by auto
  then have "s' r = s r \<and> t' r = s' r" using rec_call1 rec_call2 ctx by simp
  then have frame: "t r = s r" 
    using prefin minus_partial[of t2 t3 r] ctx prefin minus fin by auto
  then have preserve_res: "t' res = s' res" using obvious rec_call2 ctx by auto

  have "\<forall>r. r \<in> avars2 a2 \<longrightarrow> s' r = s r" using rec_call1 ctx by simp
  then have "aval2 a2 s' = aval2 a2 s" using aval2_cong[of a2 s' s] rec_call1 by simp
  then have "t' res = aval2 a1 s \<and> t' (res + 1) = aval2 a2 s" 
    using obvious preserve_res rec_call1 rec_call2 ctx by auto
  then have "t3 2 = aval2 a1 s - aval2 a2 s" using prefin minus_partial[of t2 t3 0] minus by auto
  then have "t res = aval2 (Minus2 a1 a2) s" using fin by auto
  
  then show ?case using frame by auto
next
  case (5 res a1 a2)
  note ctx = this
  from ctx obtain s' t' t2 t3 where 
    rec_call1: "(com_of_aexp2 res a1, s) \<Rightarrow> s'" and
    rec_call2: "(com_of_aexp2 (res + 1) a2, s') \<Rightarrow> t'" and
    prefin: "(0 ::= V res;; 1 ::= V (res + 1), t') \<Rightarrow> t2" and
    mult: "(mult_com, t2) \<Rightarrow> t3" and 
    fin: "(res ::= V 2, t3) \<Rightarrow> t"
  by (smt (verit, ccfv_threshold) SeqE Seq_assoc com_of_aexp2.simps(5))

  have obvious: "\<forall>r. r \<in> avars2 a2 \<longrightarrow> r < res + 1" using ctx(5) by auto
  then have "s' r = s r \<and> t' r = s' r" using rec_call1 rec_call2 ctx by simp
  then have frame: "t r = s r" 
    using prefin mult_partial[of t2 t3 r] ctx prefin mult fin by auto
  then have preserve_res: "t' res = s' res" using obvious rec_call2 ctx by auto

  have "\<forall>r. r \<in> avars2 a2 \<longrightarrow> s' r = s r" using rec_call1 ctx by simp
  then have "aval2 a2 s' = aval2 a2 s" using aval2_cong[of a2 s' s] rec_call1 by simp
  then have "t' res = aval2 a1 s \<and> t' (res + 1) = aval2 a2 s" 
    using obvious preserve_res rec_call1 rec_call2 ctx by auto
  then have "t3 2 = aval2 a1 s * aval2 a2 s" using prefin mult_partial[of t2 t3 0] mult by auto
  then have "t res = aval2 (Mult2 a1 a2) s" using fin by auto
  
  then show ?case using frame by auto
qed auto


text_raw \<open>\EndTask\<close>

(*-------------------------------------------------------------------------------------------*)

text_raw \<open>\BeginTask{20 marks (advanced)}\<close>

text \<open>Prove the termination (and therefore total correctness) of programs generated by
  @{term com_of_aexp2} (again possibly adding assumptions as in the previous task):\<close>

lemma test_termination_proof_ideas:
  "\<exists>t. (WHILE Less (N 0) (V 0) DO 0 ::= Plus (V 0) (N (-1)), s) \<Rightarrow> t"
proof-
  let ?b = "Less (N 0) (V 0)"
  let ?c = "0 ::= Plus (V 0) (N (-1))"
  show ?thesis 
  proof (induction "nat (s 0)" arbitrary: s rule: nat.induct)
    case zero
    then show ?case using WhileFalse[of ?b s] by auto
  next
    case (Suc n)
    then obtain s' where loop: "(?c, s) \<Rightarrow> s'" by auto
    then have "n = nat (s' 0)" using "Suc"(2) by auto
    then have inner_loop_terminates: "\<exists>t. (WHILE ?b DO ?c, s') \<Rightarrow> t" using "Suc"(1) by simp
    
    have cond_true: "bval ?b s" using "Suc" by simp
    then show ?case using loop inner_loop_terminates 
      WhileTrue[of ?b s ?c s'] by auto
  qed
qed


lemma chain_terminates:
  "\<exists>s'. (c, s) \<Rightarrow> s' \<and> (\<exists>t. (c', s') \<Rightarrow> t) \<Longrightarrow> \<exists>t. (c;; c', s) \<Rightarrow> t"
  by auto
lemma chain_terminates_prepend:
  "(c, s) \<Rightarrow> s' \<Longrightarrow> \<exists>t. (c', s') \<Rightarrow> t \<Longrightarrow> \<exists>t'. (c;; c', s) \<Rightarrow> t'"
  by auto
lemma chain_terminates_append:
  "\<exists>s'. (c, s) \<Rightarrow> s' \<Longrightarrow> \<forall>s'. \<exists>t. (c', s') \<Rightarrow> t  \<Longrightarrow> \<exists>t'. (c;; c', s) \<Rightarrow> t'"
  by auto
lemma if_terminates:
  "(bval b s \<Longrightarrow> \<exists>t. (c1, s) \<Rightarrow> t) \<Longrightarrow> (\<not>bval b s \<Longrightarrow> \<exists>t. (c2, s) \<Rightarrow> t) \<Longrightarrow> \<exists>t. (IF b THEN c1 ELSE c2, s) \<Rightarrow> t"
  by auto

lemma bval_eq[simp]: "bval (eq a1 a2) s \<longleftrightarrow> (aval a1 s = aval a2 s)" unfolding eq_def by auto

lemma minus_com_terminates:
  "\<exists>t. (minus_com, s) \<Rightarrow> t"
unfolding minus_com_def proof (rule chain_terminates_prepend)
  let ?b = "Not (eq (V 0) (Plus (V 1) (V 2)))"
  let ?c = "IF Less (V 1) (N 0) THEN 2 ::= Plus (V 2) (N 1)
                                ELSE 2 ::= Plus (V 2) (N (-1))"
  show "(2 ::= V 0, s) \<Rightarrow> s(2 := s 0)" by (simp add: assign_simp)

  let ?Between = "\<lambda>r. if r 1 < 0 then r 0 \<le> r 2 \<and> r 2 \<le> r 0 - r 1
                                 else r 0 - r 1 \<le> r 2 \<and> r 2 \<le> r 0"
  have "\<And>r. ?Between r \<Longrightarrow> \<exists>t. (WHILE ?b DO ?c, r) \<Rightarrow> t" proof-
    fix r
    show "?Between r \<Longrightarrow> \<exists>t. (WHILE ?b DO ?c, r) \<Rightarrow> t"
    proof (induction "nat (abs (r 2 - (r 0 - r 1)))" arbitrary: r rule: nat_induct)
      case 0
      hence "\<not>bval ?b r" by auto
      moreover obtain t where "(?c, r) \<Rightarrow> t" by (meson Assign IfFalse IfTrue)
      ultimately show ?case using WhileFalse by force
    next
      case (Suc n)
      let ?r' = "r(2 := if r 1 < 0 then r 2 + 1 else r 2 - 1)"
      from "Suc" have body: "(?c, r) \<Rightarrow> ?r'" by (simp add: IfFalse IfTrue assign_simp)
      moreover have "n = nat (abs (?r' 2 - (?r' 0 - ?r' 1)))" using "Suc" by auto
      moreover have bet: "?Between ?r'" using "Suc"(2) "Suc"(3) by auto
      ultimately have inner_termination: "\<exists>t. (WHILE ?b DO ?c, ?r') \<Rightarrow> t" using "Suc"(1) by auto
  
      have "bval ?b r" using "Suc" bet by auto
      thus ?case using body inner_termination
          WhileTrue[of ?b r ?c ?r'] by auto
    qed 
  qed
  thus "\<exists>t. (WHILE ?b DO ?c, s(2 := s 0)) \<Rightarrow> t" by auto
qed

lemma mult_pos_com_terminates:
  "s 0 \<ge> 0 \<Longrightarrow> \<exists>t. (mult_pos_com, s) \<Rightarrow> t"
unfolding mult_pos_com_def proof (rule chain_terminates_prepend)
  let ?b = "Less (V 3) (V 0)"
  let ?c = "2 ::= Plus (V 2) (V 1);; 3 ::= Plus (V 3) (N 1)"
  show "(2 ::= N 0;; 3 ::= N 0, s) \<Rightarrow> s(2 := 0, 3:= 0)" by (simp add: Seq assign_simp)

  let ?Valid = "\<lambda>r. r 3 \<le> r 0"
  have "\<And>r. ?Valid r \<Longrightarrow> \<exists>t. (WHILE ?b DO ?c, r) \<Rightarrow> t" proof-
    fix r
    show "?Valid r \<Longrightarrow> \<exists>t. (WHILE ?b DO ?c, r) \<Rightarrow> t"
    proof (induction "nat (r 0 - r 3)" arbitrary: r rule: nat_induct)
      case 0
      hence "\<not>bval ?b r" by auto
      moreover obtain t where "(?c, r) \<Rightarrow> t" by auto
      ultimately show ?case using WhileFalse by force
    next
      case (Suc n)
      let ?r' = "r(2 := r 2 + r 1, 3 := r 3 + 1)"
      from "Suc" have body: "(?c, r) \<Rightarrow> ?r'" by (simp add: Seq assign_simp)
      moreover have "n = nat (?r' 0 - ?r' 3)" using "Suc" by auto
      moreover have bet: "?Valid ?r'" using "Suc"(2) "Suc"(3) by auto
      ultimately have inner_termination: "\<exists>t. (WHILE ?b DO ?c, ?r') \<Rightarrow> t" using "Suc"(1) by auto
  
      have "bval ?b r" using "Suc" bet by auto
      thus ?case using body inner_termination
          WhileTrue[of ?b r ?c ?r'] by auto
    qed 
  qed
  thus "s 0 \<ge> 0 \<Longrightarrow> \<exists>t. (WHILE ?b DO ?c, s(2 := 0, 3:= 0)) \<Rightarrow> t" by auto
qed

lemma unary_minus_com_terminates:
  "\<exists>t. (unary_minus_com, s) \<Rightarrow> t"
  unfolding unary_minus_com_def using minus_com_terminates 
  by (auto simp: assign_simp chain_terminates_append)

lemma mult_com_terminates:
  "\<exists>t. (mult_com, s) \<Rightarrow> t"
  unfolding mult_com_def
proof (rule if_terminates)
  let ?bv = "bval (Less (V 0) (N 0))"
  let ?fst = "unary_minus_com;; 0 ::= V 2"
  let ?snd = "mult_pos_com;; 4 ::= V 2;;
              unary_minus_com;; 0 ::= V 4;; 4 ::= V 2;;
              unary_minus_com;;
              0 ::= V 4"

  show "\<not> ?bv s \<Longrightarrow> \<exists>t. (mult_pos_com, s) \<Rightarrow> t" 
    using mult_pos_com_terminates by force

  have "?bv s \<Longrightarrow> \<exists>t. (?fst;; ?snd, s) \<Rightarrow> t" 
  proof-
    assume assm: "?bv s"
    show "\<exists>t. (?fst;; ?snd, s) \<Rightarrow> t"
    proof (rule chain_terminates[of ?fst])
      show "\<exists>s'. (?fst, s) \<Rightarrow> s' \<and> (\<exists>t. (?snd, s') \<Rightarrow> t)" 
      proof-
        obtain s' where "(?fst, s) \<Rightarrow> s'" 
          using unary_minus_com_terminates by blast
        moreover have "s' 0 \<ge> 0" 
          using assm unary_minus_partial
          by (smt (verit, ccfv_SIG) SeqE \<open>(unary_minus_com;; 0 ::= V 2, s) \<Rightarrow> s'\<close> assign_simp
              aval.simps(1,2) bval.simps(4) fun_upd_same zero_neq_numeral)
        hence "\<exists>t. (?snd, s') \<Rightarrow> t" 
          using mult_pos_com_terminates unary_minus_com_terminates 
          by (meson Assign Seq)
        ultimately show "\<exists>s'. (?fst, s) \<Rightarrow> s' \<and> (\<exists>t. (?snd, s') \<Rightarrow> t)" by blast
      qed
    qed 
  qed

  thus "?bv s \<Longrightarrow> \<exists>t. (unary_minus_com;; 0 ::= V 2;;
                       mult_pos_com;; 4 ::= V 2;;
                       unary_minus_com;; 0 ::= V 4;; 4 ::= V 2;;
                       unary_minus_com;; 0 ::= V 4, s) \<Rightarrow> t" by blast
qed
 

lemma com_of_aexp2_terminates:
  "\<exists>t. (com_of_aexp2 res e, s) \<Rightarrow> t"
proof (induction res e arbitrary: s rule: com_of_aexp2.induct)
next
  case (3 res a1 a2)
  moreover have "\<forall>s. \<exists>t. (res ::= Plus (V res) (V (res + 1)), s) \<Rightarrow> t" by auto
  ultimately show ?case using chain_terminates_append by auto
next
  case (4 res a1 a2)
  show ?case
  proof -
    obtain ii :: "(nat \<Rightarrow> int) \<Rightarrow> com \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> int" where
      f1: "\<forall>X0 X2 X3. (\<exists>X4. (X3;; X2, X0) \<Rightarrow> X4) \<longrightarrow> (X3;; X2, X0) \<Rightarrow> ii X0 X2 X3"
      by moura
    obtain iia :: "(nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" and iib :: "(nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" where
      f2: "\<forall>f. (com_of_aexp2 res a1, f) \<Rightarrow> iia f"
      using "4.IH"(1) by moura
    obtain iic :: "(nat \<Rightarrow> int) \<Rightarrow> com \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> int" where
      f3: "\<forall>f fa c ca. (ca;; c, f) \<Rightarrow> iic f c ca \<or> \<not> (ca, f) \<Rightarrow> fa \<or> (\<forall>f. \<not> (c, fa) \<Rightarrow> f)"
      using f1 by blast
    then have "\<forall>n f fa fb a aa. (com_of_aexp2 n (Minus2 a aa), fa) \<Rightarrow> iic fa (n ::= V 2) (com_of_aexp2 n a;; com_of_aexp2 (n + 1) aa;; 0 ::= V n;; 1 ::= V (n + 1);; minus_com) \<or> \<not> (n ::= V 2, fb) \<Rightarrow> f \<or> \<not> (com_of_aexp2 n a;; com_of_aexp2 (n + 1) aa;; 0 ::= V n;; 1 ::= V (n + 1);; minus_com, fa) \<Rightarrow> fb"
      by (smt (z3) com_of_aexp2.simps(4))
    then show ?thesis
      using f3 f2 by (meson "4.IH"(2) Assign minus_com_terminates)
  qed
next
  case (5 res a1 a2)
  show ?case using mult_com_terminates Seq_assoc chain_terminates_prepend chain_terminates_append 
  proof -
    obtain ii :: "(nat \<Rightarrow> int) \<Rightarrow> com \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> int" where
      f1: "\<forall>X0 X2 X3. (\<exists>X4. (X3;; X2, X0) \<Rightarrow> X4) \<longrightarrow> (X3;; X2, X0) \<Rightarrow> ii X0 X2 X3"
      by moura
    obtain iia :: "(nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" and iib :: "(nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" where
      f2: "\<forall>f. (com_of_aexp2 res a1, f) \<Rightarrow> iia f"
      using "5.IH"(1) by moura
    obtain iic :: "(nat \<Rightarrow> int) \<Rightarrow> com \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> int" where
      f3: "\<forall>f fa c ca. (ca;; c, f) \<Rightarrow> iic f c ca \<or> \<not> (ca, f) \<Rightarrow> fa \<or> (\<forall>f. \<not> (c, fa) \<Rightarrow> f)"
      using f1 by blast
    then show ?thesis
      using f3 f2
    proof -
      have "\<exists>f. (com_of_aexp2 res a1;; com_of_aexp2 (res + 1) a2, s) \<Rightarrow> f"
        using "5.IH"(2) Seq f2 by moura
      then show ?thesis
        using mult_com_terminates by fastforce
    qed
  qed
qed auto

lemma com_of_aexp2_correct_total:
  assumes "res > 4"
  and "\<forall>r. r \<in> avars2 e \<longrightarrow> r > 4 \<and> r < res"
  and "r > 4" and "r < res"
  shows "\<exists>t. (com_of_aexp2 res e, s) \<Rightarrow> t \<and> t res = aval2 e s \<and> t r = s r"
using assms com_of_aexp2_terminates com_of_aexp2_correct by blast

text_raw \<open>\EndTask\<close>

(*<*)
end
(*>*)

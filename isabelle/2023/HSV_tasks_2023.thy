theory HSV_tasks_2023 imports Complex_Main begin

section \<open> Task 1: Extending our circuit synthesiser to handle XOR gates. \<close>

text \<open> Datatype for representing simple circuits, extended with XOR gates. \<close>
datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| XOR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text \<open> Simulates a circuit given a valuation for each input wire. \<close>
fun simulate where
  "simulate (AND c1 c2) \<rho> = ((simulate c1 \<rho>) \<and> (simulate c2 \<rho>))"
| "simulate (OR c1 c2) \<rho> = ((simulate c1 \<rho>) \<or> (simulate c2 \<rho>))"
| "simulate (XOR c1 c2) \<rho> = ((simulate c1 \<rho>) \<noteq> (simulate c2 \<rho>))"
| "simulate (NOT c) \<rho> = (\<not> (simulate c \<rho>))"
| "simulate TRUE \<rho> = True"
| "simulate FALSE \<rho> = False"
| "simulate (INPUT i) \<rho> = \<rho> i"

text \<open> Equivalence between circuits. \<close> 
fun circuits_equiv (infix "\<sim>" 50) (* the "50" indicates the operator precedence *) where
  "c1 \<sim> c2 = (\<forall>\<rho>. simulate c1 \<rho> = simulate c2 \<rho>)"

text \<open> Declaring a "trans" lemma allows `\<sim>` to appear in calculation chains. \<close>
lemma[trans]: "\<lbrakk> c1 \<sim> c2; c2 \<sim> c3 \<rbrakk> \<Longrightarrow> c1 \<sim> c3" by simp

text \<open> This is an optimisation that removes XOR gates from a given circuit. It exploits 
       the following Boolean identity:

            a xor b = (a \<or> b) \<and> \<not>(a \<and> b)
     \<close>
fun elim_xor where
  "elim_xor (AND c1 c2) = 
         AND (elim_xor c1) (elim_xor c2)"
| "elim_xor (OR c1 c2) = 
         OR (elim_xor c1) (elim_xor c2)"
| "elim_xor (XOR c1 c2) = (
         let c1 = elim_xor c1; c2 = elim_xor c2 in 
         AND (OR c1 c2) (NOT (AND c1 c2)))"
| "elim_xor (NOT c) = NOT (elim_xor c)"
| "elim_xor TRUE = TRUE"
| "elim_xor FALSE = FALSE"
| "elim_xor (INPUT i) = INPUT i"

text \<open> An example of the optimisation in action. \<close>
value "elim_xor (XOR (XOR (INPUT 1) (INPUT 2)) (XOR (INPUT 3) (INPUT 4)))"


text \<open> The optimisation is sound: it does not change the circuit's behaviour. \<close>
theorem elim_xor_is_sound [simp]: "elim_xor c \<sim> c"
  apply(induct_tac c)
  apply(auto)
  apply(meson simulate.simps(1) simulate.simps(4))
  apply(meson simulate.simps(1) simulate.simps(2))
  apply(meson simulate.simps(1) simulate.simps(2) simulate.simps(4))
  apply(metis simulate.simps(1) simulate.simps(2) simulate.simps(4))
done

  



section \<open> Task 2: An optimisation that introduces XOR gates. \<close>

text \<open> This is an optimisation that seeks to introduce XOR gates into a given circuit. 
       It exploits the following Boolean identities:
     
            (a \<or> b) \<and> \<not>(a \<and> b) = a xor b
            (b \<or> a) \<and> \<not>(a \<and> b) = a xor b
            (a \<or> b) \<and> \<not>(b \<and> a) = a xor b
            (b \<or> a) \<and> \<not>(b \<and> a) = a xor b
            \<not>(a \<and> b) \<and> (a \<or> b) = a xor b
            \<not>(a \<and> b) \<and> (b \<or> a) = a xor b
            \<not>(b \<and> a) \<and> (a \<or> b) = a xor b
            \<not>(b \<and> a) \<and> (b \<or> a) = a xor b
     \<close>
fun intro_xor where
  "intro_xor (AND (OR a b) (NOT (AND c d))) = (
   let a = intro_xor a; b = intro_xor b; 
       c = intro_xor c; d = intro_xor d in
   if a=c \<and> b=d \<or> a=d \<and> b=c then XOR a b else 
   (AND (OR a b) (NOT (AND c d))))"
| "intro_xor (AND (NOT (AND a b)) (OR c d)) = (
   let a = intro_xor a; b = intro_xor b; 
       c = intro_xor c; d = intro_xor d in
   if a=c \<and> b=d \<or> a=d \<and> b=c then XOR a b else 
   (AND (NOT (AND a b)) (OR c d)))"
| "intro_xor (NOT c) = NOT (intro_xor c)"
| "intro_xor (AND c1 c2) = 
           AND (intro_xor c1) (intro_xor c2)"
| "intro_xor (OR c1 c2) = 
           OR (intro_xor c1) (intro_xor c2)"
| "intro_xor (XOR c1 c2) = 
           XOR (intro_xor c1) (intro_xor c2)"
| "intro_xor TRUE = TRUE"
| "intro_xor FALSE = FALSE"
| "intro_xor (INPUT i) = INPUT i"

value "intro_xor (AND (OR (INPUT 1) (INPUT 2)) (NOT (AND (INPUT 2) (INPUT 1))))"

thm intro_xor.simps(1)
thm intro_xor.simps(2)
thm intro_xor.simps(4)


text \<open> The optimisation is sound: it does not change the circuit's behaviour. \<close>
theorem intro_xor_is_sound [simp]: "intro_xor c \<sim> c"
proof(induct c)
  case (NOT c)
  then show ?case by simp
next
  case (AND c1 c2)
  then show ?case sorry
  case (OR c1 c2)
  then show ?case by simp
next
  case (XOR c1 c2)
  then show ?case by simp
next
  case TRUE
  then show ?case by simp
next
  case FALSE
  then show ?case by simp
next
  case (INPUT x)
  then show ?case by simp
qed



section \<open> Task 3: A clone function for making lists. \<close>

text \<open> `clone n x` creates a list comprising `n` copies of `x`. \<close>
fun clone :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  "clone 0 x = []"
| "clone (Suc n) x = x # clone n x"

value "clone 5 ''Ni''"
value "(clone 5 ''Ni'')"

lemma rev_equal_length: "length (clone n x) = length (rev (clone n x))" by auto

lemma suc_zero_is_one: "Suc 0 = 1" by auto

lemma suc_x_is_xpone: "\<lbrakk> x \<in> \<nat> ; y = x + 1 \<rbrakk> \<Longrightarrow> Suc x = y " by auto

(*lemma next_item_is_equal: " \<lbrakk> i \<in> \<nat> ; j = Suc i ;  j \<le> n \<rbrakk> \<Longrightarrow> (clone n x)!i = (clone n x)!j"
proof (induct i arbitrary: n)
  case 0
  then show ?case
  proof (auto)
    have "(clone n x) !0 = x"
      by (metis "0.prems"(2) "0.prems"(3) One_nat_def add.left_neutral clone.elims leD lessI nth_Cons_0)
    have "clone (Suc 0) x = x # clone 0 x"
      by (simp add: clone.simps(2))
    hence "clone (Suc i) x = x # clone i x" by simp
    hence "clone j x = x # clone i x" 
  qed
    
next
  case (Suc i)
  then show ?case sorry
qed 
  
qed*)

lemma commute_clone_x: "[x] @ clone n x = clone n x @ [x]"
  apply(induct_tac n)
   apply(auto)

  done

lemma rev_clone: "rev (clone n x) = clone n x"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "[x] @ clone (Suc n) x = x # (clone (Suc n) x)" by auto
  have "clone (Suc n) x = [x] @ clone n x" by auto
  hence "rev (clone (Suc n) x) = rev ([x] @ clone n x)"
    by simp 
  hence "rev (clone (Suc n) x) = rev (clone n x) @ [x]"
    using clone.simps(2) rev.simps(2) by force
  hence "rev (clone (Suc n) x) = clone n x @ [x]"
    using Suc by force
  hence "rev (clone (Suc n) x) = [x] @ clone n x" using commute_clone_x by metis
  hence "rev (clone (Suc n) x) = clone (Suc n) x"
    by auto
  thus ?case by auto
qed


section \<open> Task 4: Analogue-to-digital conversion. \<close>

text \<open> Interprets a list of booleans as a binary number written _backwards_ (LSB first).  \<close>
fun backward_bits_to_nat :: "bool list \<Rightarrow> nat"
  where
    "backward_bits_to_nat (False # bs) = 2 * backward_bits_to_nat bs"
  | "backward_bits_to_nat (True # bs) = 2 * backward_bits_to_nat bs + 1"
  | "backward_bits_to_nat [] = 0"

text \<open> Interprets a list of booleans as a binary number (written in the normal way, MSB first).  \<close>
definition bits_to_nat :: "bool list \<Rightarrow> nat"
where
  "bits_to_nat bs = backward_bits_to_nat (rev bs)"

type_synonym sar = "bool list * bool list"

text \<open> This function performs one step of the ADC. The SAR is represented using two lists, 
       (r1, r2), with r1 representing the first part of the SAR and r2 representing 
       the second part. As the ADC progresses, r1 grows and r2 shrinks. \<close>
fun adc_step :: "real \<Rightarrow> sar \<Rightarrow> sar"
where
  "adc_step i (r1, r2) = (
    let r = r1 @ (True # tl r2) in
    let cmp = real (bits_to_nat r) \<le> i in
    (r1 @ [cmp], tl r2))"

text \<open> A worked example stepping through the ADC process. \<close>
lemma "adc_step 9.4 ([], [False, False, False, False]) = ([True],  [False, False, False])" by eval
lemma "adc_step 9.4 ([True],    [False, False, False]) = ([True, False],  [False, False])" by eval
lemma "adc_step 9.4 ([True, False],    [False, False]) = ([True, False, False],  [False])" by eval
lemma "adc_step 9.4 ([True, False, False],    [False]) = ([True, False, False, True], [])" by eval

text \<open> This function keeps calling `adc_step` until all bits have been processed. \<close>
fun adc_helper :: "real \<Rightarrow> sar \<Rightarrow> bool list"
where
  "adc_helper i (r1, []) = r1"
| "adc_helper i (r1, r2) = adc_helper i (adc_step i (r1, r2))"

text \<open> Top-level entry point for the ADC. It zeroes the SAR then calls `adc_helper`. \<close>
definition adc :: "nat \<Rightarrow> real \<Rightarrow> bool list"
where
  "adc w i = adc_helper i ([], clone w False)"

text \<open> Trying out the ADC with various inputs and various bitwidths. \<close>
value "adc 5 9.4"
value "adc 4 9.4"
value "adc 3 9.4"
value "adc 4 5.4"

text \<open> This theorem says that the output of ADC on input i is always less than or equal to i. 
       NB: this is quite a weak theorem, because to capture the behaviour of ADC more fully, 
       we would also want to bound the ADC's output from below. But that property is more 
       complicated because it relies on choosing an appropriate bitwidth, so we'll leave that 
       for another day. \<close>

theorem addition_of_true_is_bigger: "bits_to_nat(l1 @ [True]) > bits_to_nat(l1 @ [False])" 
proof(induct l1)
  case Nil
  then have "backward_bits_to_nat(True # []) > backward_bits_to_nat(False # [])"
    by simp
  moreover have "rev([] @ [True]) = [True]" 
    by simp
  then have "bits_to_nat([] @ [True]) = backward_bits_to_nat [True]" 
    using bits_to_nat_def by auto
  moreover have "rev([] @ [False]) = [False]"
    by simp
  then have "bits_to_nat([] @ [False]) = backward_bits_to_nat [False]" 
    using bits_to_nat_def by auto
  then show ?case 
    using calculation(2) by force
next
  case (Cons a l1)
  have "rev ((Cons a l1) @ [True]) = [True] @ rev (Cons a l1)"
    by simp 
  then have "backward_bits_to_nat ([True] @ rev (Cons a l1)) = 2*backward_bits_to_nat (rev (Cons a l1)) + 1"
    by simp
  moreover have "rev ((Cons a l1) @ [False]) = [False] @ rev (Cons a l1)"
    by simp 
  then have "backward_bits_to_nat ([False] @ rev (Cons a l1)) = 2*backward_bits_to_nat (rev (Cons a l1))"
    by simp
  then show ?case
    by (simp add: bits_to_nat_def)
qed


theorem larger_of_two_bool_lists: "\<lbrakk> length l1 = length l2 ; backward_bits_to_nat(l1) > backward_bits_to_nat(l2)  \<rbrakk> \<Longrightarrow> 
 backward_bits_to_nat(l3 @ l1) > backward_bits_to_nat(l3 @ l2)" sorry

theorem value_of_true_list: "backward_bits_to_nat(clone n True) = (2^n) - 1 " 
  proof(induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n) 
    have "backward_bits_to_nat(clone (Suc n) True) = backward_bits_to_nat(True # clone n True)" 
      by simp
    then have "... = 2*backward_bits_to_nat(clone n True) + 1" 
      by simp
    then have "... = 2*((2^n) - 1) + 1"
      by (simp add: Suc)
    then have "... = 2*(2^n) - 2 + 1" 
      by simp 
    then have "... = ((2^(n+1)) - 1)"
      by (smt (verit, ccfv_threshold) Nat.add_diff_assoc2 add.commute le_add_diff_inverse2 left_add_twice mult_2 one_le_numeral one_le_power plus_1_eq_Suc power_Suc)
    then show ?case
      using Suc Suc_eq_plus1 \<open>2 * (2 ^ n - 1) + 1 = 2 * 2 ^ n - 2 + 1\<close> \<open>backward_bits_to_nat (True # clone n True) = 2 * backward_bits_to_nat (clone n True) + 1\<close> \<open>backward_bits_to_nat (clone (Suc n) True) = backward_bits_to_nat (True # clone n True)\<close> by presburger
  qed

theorem bool_list_bit_shift:  "backward_bits_to_nat((clone n False) @ l1) = backward_bits_to_nat(l1)*(2^n)"
proof (induct n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "backward_bits_to_nat((clone (Suc n) False) @ l1) = backward_bits_to_nat([False] @ (clone n False) @ l1)" 
    by simp
  then have "... = 2*backward_bits_to_nat((clone n False) @ l1)"
    by simp
  then have "... = 2*backward_bits_to_nat(l1)*(2^n)"
    by (simp add: Suc)
  then have "... = (2^(Suc n))*backward_bits_to_nat(l1)"
    by simp
  then show ?case
    using \<open>2 * backward_bits_to_nat (clone n False @ l1) = 2 * backward_bits_to_nat l1 * 2 ^ n\<close> by auto
qed

theorem bool_list_addition: "backward_bits_to_nat (l1 @ l2) = (2^(length l1))*backward_bits_to_nat(l2) + backward_bits_to_nat(l1)"
proof (induct l1)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l1)  
  have "length (a # l1) = length (l1) + 1"
    by simp
  then show ?case 
  proof (cases a)
    case True
 then have "backward_bits_to_nat ((a # l1) @ l2) = 2*backward_bits_to_nat(l1 @ l2) + 1" 
    by simp
  then have "... = 2*((2^(length l1))*backward_bits_to_nat(l2) + backward_bits_to_nat(l1)) + 1"
    by (simp add: local.Cons)
  then have "... = (2^((length l1) + 1))*backward_bits_to_nat(l2) + (2*backward_bits_to_nat(l1) + 1)" 
    by simp
  then have "... = 2^(length (a # l1))*backward_bits_to_nat(l2) + backward_bits_to_nat (a # l1)"
    using True \<open>length (a # l1) = length l1 + 1\<close> backward_bits_to_nat.simps(2) by presburger
    then show ?thesis 
      by (simp add: True local.Cons)
  next
    case False
then have "backward_bits_to_nat ((a # l1) @ l2) = 2*backward_bits_to_nat(l1 @ l2)" 
    by simp
  then have "... = 2*((2^(length l1))*backward_bits_to_nat(l2) + backward_bits_to_nat(l1))"
    by (simp add: local.Cons)
  then have "... = (2^((length l1) + 1))*backward_bits_to_nat(l2) + 2*backward_bits_to_nat(l1)" 
    by simp
  then have "... = 2^(length (a # l1))*backward_bits_to_nat(l2) + backward_bits_to_nat (a # l1)" 
    using False \<open>length (a # l1) = length l1 + 1\<close> backward_bits_to_nat.simps(1) by presburger
    then show ?thesis 
      using False local.Cons by fastforce
  qed
qed

theorem true_sandwich_is_bigger: "backward_bits_to_nat (l1 @ [True] @ l2) > backward_bits_to_nat (l1 @ [False] @ l2)" using bool_list_addition and addition_of_true_is_bigger
  by simp

(*" \<lbrakk> i > 0; n > 0; real((bits_to_nat(l1 @ clone n False))) \<le> i ; 
                                        compar = (real((bits_to_nat(l1 @ [True] @ tl (clone n False)))) \<le> i) \<rbrakk>
                                         \<Longrightarrow> real((bits_to_nat(l1 @ [compar] @ tl (clone n False)))) \<le> i"*)

theorem adc_step_not_greater_than_i: 
  assumes " i > 0"
  assumes "n > 0" 
  assumes "real((bits_to_nat(l1 @ clone n False))) \<le> i" 
  assumes " compar = (real((bits_to_nat(l1 @ [True] @ tl (clone n False)))) \<le> i)"
  shows "real((bits_to_nat(l1 @ [compar] @ tl (clone n False)))) \<le> i"
proof  (cases compar)
  have "bits_to_nat(l1 @ clone n False) = backward_bits_to_nat((clone n False) @ (rev l1))" using rev_clone
    by (metis bits_to_nat_def rev_append) 
  then have "... = (2^n)*backward_bits_to_nat(rev l1)" using bool_list_bit_shift
    by simp
  case True
  have  "i \<ge> real((bits_to_nat(l1 @ [True] @ tl (clone n False))))" 
    using True assms(4) by auto
  then show ?thesis
    using True by auto
next
  case False
  have "real((bits_to_nat(l1 @ clone n False))) \<le> i" using False assms(3) by auto
  have "tl (clone n False) = clone (n-1) False"
    using assms(2) gr0_conv_Suc by force
  then have "clone n False = [False] @ tl (clone n False)"
    by (metis Nat.lessE append_Cons append_Nil assms(2) clone.simps(2) diff_Suc_1) 
  then have "bits_to_nat(l1 @ clone n False) = bits_to_nat(l1 @ [False] @ tl (clone n False))" 
    by simp  
  then show ?thesis 
    using False assms(3) by fastforce
qed

theorem adc_helper_not_greater_than_i: 
  assumes " i > 0"
  assumes "n > 0" 
  assumes "real(bits_to_nat(r1 @ clone n False)) \<le> i"
  assumes "(l1, l2) = adc_step i (r1, clone n False)"
  shows "real(bits_to_nat(l1 @ l2)) \<le> i" 
 
proof- 
  have "l2 = tl (clone n False)" 
    using assms(4) by auto
  have "l1 = r1 @ [(real(bits_to_nat(r1 @ [True] @ tl (clone n False))) \<le> i)]" 
    using assms(4) by auto
  then have "real(bits_to_nat(l1 @ l2)) \<le> i" using adc_step_not_greater_than_i 
    by (simp add: \<open>l2 = tl (clone n False)\<close> assms(1) assms(2) assms(3))
  then have "bits_to_nat(l1 @ l2) \<le> i" 
    by simp
  from this show "real(bits_to_nat(l1 @ l2)) \<le> i" 
    by simp
qed 

theorem i_zero_adc_helper_not_greater_than_i_Nil: 
  assumes " i = 0"
  assumes "n > 0" 
  assumes "bits_to_nat([] @ clone n False) \<le> i"
  assumes "(l1, l2) = adc_step i ([], clone n False)"
  shows "real(bits_to_nat(l1 @ l2)) \<le> i" 
proof -
have "backward_bits_to_nat(clone n False @ []) = 0" using bool_list_bit_shift
    using backward_bits_to_nat.simps(3) by presburger 
  then have "bits_to_nat([] @ clone n False) = 0" using rev_clone 
    by (metis append.right_neutral append_self_conv2 bits_to_nat_def) 
  moreover have "backward_bits_to_nat(clone n False @ [True] @ []) > 0" using bool_list_bit_shift 
    by simp
  then have "(real(bits_to_nat([] @ [True] @ tl (clone n False))) \<le> i) = False" using rev_clone
    by (metis append.left_neutral append_Cons assms(1) bits_to_nat_def bot_nat_0.extremum linorder_not_less of_nat_0 of_nat_le_0_iff rev.simps(2) true_sandwich_is_bigger)
  then have "backward_bits_to_nat(rev (tl (clone n False)) @ [(real(bits_to_nat([] @ [True] @  tl (clone n False))) \<le> i)] @ []) = 0" 
    using bool_list_bit_shift and rev_clone 
    by (smt (verit) \<open>backward_bits_to_nat (clone n False @ []) = 0\<close> add_is_0 append.right_neutral backward_bits_to_nat.elims backward_bits_to_nat.simps(1) list.sel(2) list.sel(3) mult_cancel2 nat_1_add_1 power2_eq_square rev.simps(2) zero_neq_numeral zero_power2) 
  then have "(real(bits_to_nat([] @ [(real(bits_to_nat([] @ [True] @ tl (clone n False))) \<le> i)] @ tl (clone n False)))) = 0" 
    using bits_to_nat_def by auto
  then have "... \<le> i" 
    by simp
  moreover have "adc_step i ([], clone n False) = ([] @ [(real(bits_to_nat([] @ [True] @ tl (clone n False))) \<le> i)], tl (clone n False))" 
    by simp
  then have "... = ([] @ [False], tl(clone n False))" 
    using \<open>(real (bits_to_nat ([] @ [True] @ tl (clone n False))) \<le> real i) = False\<close> by auto
  then have "... = (l1, l2)" 
    using \<open>adc_step (real i) ([], clone n False) = ([] @ [real (bits_to_nat ([] @ [True] @ tl (clone n False))) \<le> real i], tl (clone n False))\<close> assms(4) by presburger
  have "real(bits_to_nat([] @ [False] @ tl(clone n False))) = 0"
     using \<open>(real (bits_to_nat ([] @ [True] @ tl (clone n False))) \<le> real i) = False\<close> \<open>real (bits_to_nat ([] @ [real (bits_to_nat ([] @ [True] @ tl (clone n False))) \<le> real i] @ tl (clone n False))) = 0\<close> by auto
   then have "real(bits_to_nat(l1 @ l2)) = 0" 
     using \<open>([] @ [False], tl (clone n False)) = (l1, l2)\<close> by fastforce
   then have "real(bits_to_nat(l1 @ l2)) \<le> i" 
     by simp
   thus ?thesis 
     by simp
qed

theorem i_zero_adc_helper_not_greater_than_i: 
  assumes " i = 0"
  assumes "n > 0" 
  assumes "real(bits_to_nat(r1 @ clone n False)) \<le> i"
  assumes "(l1, l2) = adc_step i (r1, clone n False)"
  shows "real(bits_to_nat(l1 @ l2)) \<le> i" 
proof -
  have "l2 = tl (clone n False)" 
    using assms(4) by auto
  have "l1 = r1 @ [(real(bits_to_nat(r1 @ [True] @ tl (clone n False))) \<le> i)]" 
    using assms(4) by auto
  have "real(backward_bits_to_nat(clone n False @ rev r1)) \<le> i" using rev_clone and assms(3) 
    by (metis bits_to_nat_def rev_append)
  then have "real(backward_bits_to_nat(rev r1)) = 0" using bool_list_bit_shift and assms(1) 
    by (metis mult_eq_0_iff of_nat_0 of_nat_le_0_iff power_eq_0_iff zero_neq_numeral)
  have "tl (clone n False) = rev (tl (clone n False))" 
    by (metis append.right_neutral append_Cons append_Nil butlast.simps(2) butlast_append butlast_rev butlast_tl commute_clone_x list.sel(3) rev_clone)
  have "clone n False = tl (clone n False) @ [False]" 
    by (metis assms(2) clone.elims commute_clone_x eq_Nil_appendI list.sel(3) neq0_conv not_Cons_self2 rotate1.simps(1) rotate1.simps(2) tl_append2)
  then have "... = rev (tl (clone n False)) @ [False]" 
    using \<open>tl (clone n False) = rev (tl (clone n False))\<close> by fastforce
  then have "real(backward_bits_to_nat(rev (tl (clone n False)) @ [False] @ rev r1)) = real(backward_bits_to_nat(clone n False @ rev r1))"
    by (metis \<open>clone n False = tl (clone n False) @ [False]\<close> append.assoc)
  then have "... \<le> i" 
    using \<open>real (backward_bits_to_nat (clone n False @ rev r1)) \<le> i\<close> by auto
  then have "real(backward_bits_to_nat(rev (tl (clone n False)) @ [True] @ rev r1)) > real(backward_bits_to_nat(rev (tl (clone n False)) @ [False] @ rev r1))"
    using true_sandwich_is_bigger 
    by simp
  then have "real(backward_bits_to_nat(rev (tl (clone n False)) @ [True] @ rev r1)) > i" using assms(1)
    by simp
  then have "real(bits_to_nat(r1 @ [True] @ tl (clone n False))) > i" 
    using bits_to_nat_def by auto
  then have "False = (real(bits_to_nat(r1 @ [True] @ tl (clone n False))) \<le> i)" 
    by simp
  then have "l1 = r1 @ [False]" 
    by (simp add: \<open>l1 = r1 @ [real (bits_to_nat (r1 @ [True] @ tl (clone n False))) \<le> i]\<close>)
  then have "l1 @ l2 = r1 @ clone n False" 
    by (metis \<open>clone n False = tl (clone n False) @ [False]\<close> \<open>l2 = tl (clone n False)\<close> \<open>tl (clone n False) = rev (tl (clone n False))\<close> append_assoc rev_append rev_clone rev_singleton_conv)
  then have "real(bits_to_nat(l1 @ l2)) = real(bits_to_nat(r1 @ clone n False))" 
    by simp
  then have "... \<le> i" using assms(3) 
    by simp
  thus ?thesis 
    using \<open>l1 @ l2 = r1 @ clone n False\<close> by fastforce
qed

theorem l2_is_list_of_Falses:
   assumes " i \<ge> 0"
  assumes "n > 0" 
  assumes "real(bits_to_nat(r1 @ clone n False)) \<le> i"
  assumes "(l1, l2) = adc_step i (r1, clone n False)"
  shows "l2 = clone (n-1) False" 
proof -
  have "tl (clone n False) = clone (n-1) False" 
    using assms(2) gr0_conv_Suc by fastforce
  have "l2 = tl (clone n False)" 
    using assms(4) by fastforce
  then have "... = clone (n-1) False" 
    using \<open>tl (clone n False) = clone (n - 1) False\<close> by fastforce
  thus ?thesis 
    using \<open>l2 = tl (clone n False)\<close> by fastforce
qed

theorem "adc_helper_step": 
  assumes "i \<ge> 0"
  assumes "r2 \<noteq> Nil"
  shows "adc_helper i (r1, r2) = adc_helper i (adc_step i (r1, r2))" 
  by (metis adc_helper.simps(2) assms(2) min_list.cases)

theorem "clone_list_not_nil":
  assumes "n > 0"
  shows "clone n False \<noteq> Nil"
proof (auto)
  have "clone 0 False = []" 
    by simp
  have "False # Nil \<noteq> Nil" 
    by simp
  assume "clone n False = Nil"
  then have "clone n False = []" 
    by simp
  then have "n = 0" 
    using not0_implies_Suc by fastforce
  then have "clone n False \<noteq> Nil" using assms(1) 
    by simp
  with `clone n False = Nil` show False 
    by simp
qed

theorem "adc_helper_adc_step": 
  assumes "i \<ge> 0"
  assumes "n > 0"
  assumes "real(bits_to_nat(r1 @ clone n False)) \<le> i"
  assumes "(l1, l2) = adc_step i (r1, clone n False)"
  shows "adc_helper i (r1, clone n False) = adc_helper i (l1, l2)" and "real(bits_to_nat(l1 @ l2)) \<le> i" and
 "l2 = clone (n-1) False" and "l1=r1@[(real(bits_to_nat(r1 @ [True] @ clone (n-1) False)) \<le> i)]"
proof - 
  have "adc_helper i (r1, clone n False) = adc_helper i (adc_step i (r1, clone n False))"  using adc_helper_step and clone_list_not_nil
    by (simp add: assms(1) assms(2)) 
  then have "(l1, l2) = adc_step i (r1, clone n False)"
    using assms(4) by blast
  thus "adc_helper i (r1, clone n False) = adc_helper i (l1, l2)" 
    using \<open>adc_helper i (r1, clone n False) = adc_helper i (adc_step i (r1, clone n False))\<close> by fastforce
  thus "l2 = clone (n-1) False" using l2_is_list_of_Falses and assms(4) and assms(2) and assms(1) 
    by auto
  then have "l1 = r1@[(real(bits_to_nat(r1 @ [True] @ tl (clone n False))) \<le> i)]" 
    using assms(4) by force
thus  "l1=r1@[(real(bits_to_nat(r1 @ [True] @ clone (n-1) False)) \<le> i)]" 
  using \<open>l2 = clone (n - 1) False\<close> assms(4) by auto
  {
  assume "i \<noteq> 0"
  then have "real(bits_to_nat(l1 @ l2)) \<le> i" using adc_helper_not_greater_than_i
 and assms(3) and assms(4) and assms(2) 
    by simp
}
    {
  assume "i = 0"
  then have "real(bits_to_nat(l1 @ l2)) \<le> i" using i_zero_adc_helper_not_greater_than_i
 and assms(3) and assms(4) and assms(2) 
    by simp
  }
  thus "real(bits_to_nat(l1 @ l2)) \<le> i"
    using \<open>i \<noteq> 0 \<Longrightarrow> real (bits_to_nat (l1 @ l2)) \<le> i\<close> by blast  
qed

theorem "adc_helper_induct_step": 
  assumes "i \<ge> 0"
  assumes "n > 0"
  assumes "n-a > 0"
  assumes "a > 0"
  assumes "b1=r1@a1"
  assumes "real(bits_to_nat(r1 @ clone n False)) \<le> i"
  assumes "real(bits_to_nat(b1 @ clone (n-a) False)) \<le> i"
  assumes "adc_helper i (r1, clone n False) = adc_helper i (b1, clone (n-a) False)"
  assumes "(l1, l2) = adc_step i (b1, clone (n-a) False)"
  shows "adc_helper i (r1, clone n False) = adc_helper i (l1, l2)" and "real(bits_to_nat(l1 @ l2)) \<le> i" and
 "l2 = clone (n-(Suc a)) False" and "l1=b1@[(real(bits_to_nat(b1 @ [True] @ clone (n-(Suc a)) False)) \<le> i)]"
proof -
  have "adc_helper i (b1, clone (n-a) False) = adc_helper i (adc_step i (b1, clone (n-a) False))"  using adc_helper_step and clone_list_not_nil
    using assms(1) assms(3) by presburger 
  then have "(l1, l2) = adc_step i (b1, clone (n-a) False)"
    using assms(9) by blast 
  then have  "l2 = clone ((n-a)-1) False" using l2_is_list_of_Falses and assms(9) and assms(3) and assms(1) and assms(7) 
    by blast   
  then have "... = clone (n-(Suc a)) False"
    by simp 
  thus "adc_helper i (r1, clone n False) = adc_helper i (l1, l2)"
    using \<open>adc_helper i (b1, clone (n - a) False) = adc_helper i (adc_step i (b1, clone (n - a) False))\<close> assms(8) assms(9) by presburger
  thus "l2 = clone (n-(Suc a)) False" 
    using \<open>clone (n - a - 1) False = clone (n - Suc a) False\<close> \<open>l2 = clone (n - a - 1) False\<close> by blast
  thus "l1=b1@[(real(bits_to_nat(b1 @ [True] @ clone (n-(Suc a)) False)) \<le> i)]" 
    using assms(9) by auto
  thus "real(bits_to_nat(l1 @ l2)) \<le> i"
    using adc_helper_adc_step(2) assms(1) assms(3) assms(7) assms(9) by blast
qed

thm adc_helper_induct_step
thm adc_helper.induct[of "\<lambda>i p. length(adc_helper i p) = length (fst p) + length (snd p)"]

theorem "induction_length_addition":
  shows "length(adc_helper i p) = length (fst p) + length (snd p)"
proof (induct rule: adc_helper.induct[of "\<lambda>i p. length(adc_helper i p) = length (fst p) + length (snd p)"])
  case (1 i r1)
  then show ?case by simp
next
  case (2 i r1 v va)
  have "length (fst(adc_step i (r1, v # va))) = length (r1 @ [(real(bits_to_nat(r1 @ [True] @ tl (v # va))) \<le> i)])"  
    by simp
  then have "... = length r1 + 1" 
    by simp
  have "length (snd(adc_step i (r1, v#va))) = length (tl (v # va))" 
    by simp
  then have " ... = length (v # va) - 1" 
    by simp
  then have "length (fst(adc_step i (r1, v # va))) + length (snd(adc_step i (r1, v#va))) = length r1 + length (v # va)" 
    by simp
  have "length (adc_helper i (adc_step i (r1, v # va))) = length (adc_helper i (r1, v # va))" 
    by simp
  then have "... = length (fst(adc_step i (r1, v # va))) + length (snd(adc_step i (r1, v#va)))" 
    using "2" by auto
  then have "... = length r1 + length (v # va)" 
    by simp
  then show ?case 
    using "2" by auto
qed



(*lemma remove_all_true_is_clone:
  assumes "removeAll True l1 = l1"
  shows "l1 = clone (length l1) False" using assms 
proof (induct l1)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a l1) 
  {assume "a = True"
    then have "(removeAll True [a]) = []" 
      by simp
    have "removeAll True (Cons a l1) = (removeAll True [a]) @ removeAll True l1" 
      by simp  
  then have "... = removeAll True l1" 
    using \<open>removeAll True [a] = []\<close> by blast
  then have "... = l1" using assms 
    by (metis Cons.prems \<open>removeAll True (a # l1) = removeAll True [a] @ removeAll True l1\<close> impossible_Cons length_removeAll_less_eq)
  then have "... \<noteq> (Cons a l1)" 
    by simp
  with `removeAll True (a # l1) = a # l1` show False }
  {assume "a = False"
    then have "(removeAll True [a]) = []" 
      by simp
    have "removeAll True (Cons a l1) = (removeAll True [a]) @ removeAll True l1" 
      by simp  
  then have "... = removeAll True l1" 
    using \<open>removeAll True [a] = []\<close> by blast
  then have "... = l1" using assms 
    by (metis Cons.prems \<open>removeAll True (a # l1) = removeAll True [a] @ removeAll True l1\<close> impossible_Cons length_removeAll_less_eq)
  then have "... \<noteq> (Cons a l1)" 
    by simp
  with `removeAll True (a # l1) = a # l1` show False }
  
  then show ?case 
  next
    case False
    then show ?thesis sorry
  qed
qed*)

theorem "adc_helper_induct": 
  assumes "i \<ge> 0"
  assumes "length (snd p) > 0"
  assumes "snd p = clone (length (snd p)) False"
  assumes "real(bits_to_nat(fst p @ snd p)) \<le> i"
  shows "real(bits_to_nat(adc_helper i p)) \<le> i" using assms
proof (induct rule:adc_helper.induct)
  case (1 i r1)
  then show ?case 
    by simp
next
  case (2 i r1 v va)
  then have "snd (r1, v # va) = clone (length (snd (r1, v # va))) False" 
    by simp
  then have "v # va = clone (length (snd (r1, v # va))) False" 
    by simp
  then have "... = clone (length  (v # va)) False" 
    by simp
  then have "snd (adc_step i (r1, v # va)) = tl (v # va)" 
    by simp
  then have "... = tl (clone (length  (v # va)) False)" 
    using \<open>v # va = clone (length (snd (r1, v # va))) False\<close> by fastforce
  then have "... = clone (length  (v # va) - 1) False" 
    by simp
  then have "... = clone (length (tl (v # va))) False" 
    by simp
  then have fact1: "snd (adc_step i (r1, v # va)) = clone (length (snd (adc_step i (r1, v # va)))) False" 
    using \<open>v # va = clone (length (snd (r1, v # va))) False\<close> by auto
  {assume "i > 0" and "length (snd (adc_step i (r1, v # va))) > 0"
    then have "real (bits_to_nat (fst (adc_step i (r1, v # va)) @ snd (adc_step i (r1, v # va)))) \<le> i" using adc_helper_not_greater_than_i and "2.prems" 
      by (metis prod.exhaust_sel)
    }
  {assume "i = 0"and "length (snd (adc_step i (r1, v # va))) > 0"
    then have "real (bits_to_nat (fst (adc_step i (r1, v # va)) @ snd (adc_step i (r1, v # va)))) \<le> i" using i_zero_adc_helper_not_greater_than_i and "2.prems"  
      by (smt (verit) dual_order.trans prod.exhaust_sel)
  }
  {assume "length (snd (adc_step i (r1, v # va))) = 0"
    assume "compar = (real (bits_to_nat(r1 @ [True])) \<le> i)" 
    have "tl (v # va) = snd (adc_step i (r1, v # va))" 
      by simp
    then have step_is_Nil: "... = []" using \<open>length (snd (adc_step i (r1, v # va))) = 0\<close> 
      by simp
    then have "real (bits_to_nat (fst (adc_step i (r1, v # va)) @ snd (adc_step i (r1, v # va)))) = real (bits_to_nat (fst (adc_step i (r1, v # va))))" 
      by simp
    then have "... = real (bits_to_nat (r1 @ [(real (bits_to_nat(r1 @ [True] @ tl (v # va))) \<le> i)]))" 
      by simp 
    then have "... = real (bits_to_nat (r1 @ [compar]))" using step_is_Nil and \<open>compar = (real (bits_to_nat(r1 @ [True])) \<le> i)\<close> 
      by simp
    then have "... \<le> i" proof (cases compar)
      case True
      then have "real (bits_to_nat(r1 @ [True])) \<le> i" using  \<open>compar = (real (bits_to_nat(r1 @ [True])) \<le> i)\<close> 
        by simp
      then show ?thesis using True 
        by simp
    next
      case False
       have "v # va = [v]" using step_is_Nil 
           by simp
       then have "real (bits_to_nat(fst (r1, v # va) @ snd (r1, v # va))) = real (bits_to_nat(r1 @ [v]))" 
            by simp 
       then have "... \<le> i" using "2.prems"(4) 
            by simp
      then show ?thesis proof (cases v)
        case True
        then show ?thesis using addition_of_true_is_bigger 
          using \<open>compar = (real (bits_to_nat (r1 @ [True])) \<le> i)\<close> \<open>real (bits_to_nat (r1 @ [v])) \<le> i\<close> by presburger
      next
        case False
        then show ?thesis 
          using \<open>compar = (real (bits_to_nat (r1 @ [True])) \<le> i)\<close> \<open>real (bits_to_nat (r1 @ [v])) \<le> i\<close> by auto
      qed
    qed
    }

  then have fact2: "real (bits_to_nat (fst (adc_step i (r1, v # va)) @ snd (adc_step i (r1, v # va)))) \<le> i" using "2.prems" 
    by (smt (verit) adc_helper_adc_step(2) prod.collapse)
  then show ?case using "2" and fact1 and fact2 
    by fastforce
qed

(*proof -
 have "real(bits_to_nat(clone n False)) = real(backward_bits_to_nat(rev (clone n False)))"
    using bits_to_nat_def by auto
  then have "... = real(backward_bits_to_nat(clone n False))" using rev_clone 
    by metis
  then have "... = real(backward_bits_to_nat([False] @ clone (n-1) False))"
    by (metis Suc_pred' append_Cons append_Nil assms(2) clone.simps(2))
  then have "... = 0" using bool_list_bit_shift 
    by (metis append.right_neutral backward_bits_to_nat.simps(3) mult_0 of_nat_eq_0_iff)
  then have "real(bits_to_nat([] @ clone n False)) \<le> i " 
    by (simp add: \<open>real (backward_bits_to_nat (clone n False)) = real (backward_bits_to_nat ([False] @ clone (n - 1) False))\<close> \<open>real (bits_to_nat (clone n False)) = real (backward_bits_to_nat (rev (clone n False)))\<close> assms(1) rev_clone)
  obtain b1 where "butlast (adc_helper i ([], clone n False)) = b1" 
    by simp
  then have "adc_helper i ([], clone n False) = adc_helper i (b1, clone (n-(n-1)) False)" sorry
qed*)


theorem clone_list_length: "length (clone n x) = n" proof(induct n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  then show ?case 
    by simp
qed


theorem
  assumes "0 \<le> i"
  shows "real (bits_to_nat (adc w i)) \<le> i"
proof - 
  have "real (bits_to_nat (adc w i)) = real (bits_to_nat (adc_helper i ([], clone w False)))" 
    using adc_def by auto 
  have "bits_to_nat ([] @ clone w False) = backward_bits_to_nat(clone w False @ [])" using rev_clone 
    by (metis append.left_neutral append.right_neutral bits_to_nat_def) 
  then have "... = 0" using bool_list_bit_shift 
    using backward_bits_to_nat.simps(3) by presburger
  then have "real(bits_to_nat ([] @ clone w False)) \<le> i"  
    using \<open>bits_to_nat ([] @ clone w False) = backward_bits_to_nat (clone w False @ [])\<close> assms by force
  {assume "w > 0"
    have "length (clone w False) = w" using clone_list_length 
      by metis
    then have "... > 0" 
      by (simp add: \<open>0 < w\<close>)
    then have "clone w False = clone (length (clone w False)) False" 
      using \<open>length (clone w False) = w\<close> by auto
    then have " real (bits_to_nat (adc_helper i ([], clone w False))) \<le> i" using adc_helper_induct 
      by (metis \<open>0 < w\<close> \<open>length (clone w False) = w\<close> \<open>real (bits_to_nat ([] @ clone w False)) \<le> i\<close> assms fst_eqD snd_eqD)
      then have "real (bits_to_nat (adc w i)) \<le> i" 
        by (simp add: adc_def)
  }
  {assume "w = 0"
    then have "clone w False = []" 
      by simp 
    then have "real (bits_to_nat (adc_helper i ([], clone w False))) = real (bits_to_nat (adc_helper i ([], [])))" 
      by simp
    then have "... = 0" 
      using \<open>bits_to_nat ([] @ clone w False) = backward_bits_to_nat (clone w False @ [])\<close> \<open>clone w False = []\<close> by auto
    then have "real (bits_to_nat (adc_helper i ([], clone w False))) \<le> i" 
      by (simp add: \<open>clone w False = []\<close> assms)
      then have "real (bits_to_nat (adc w i)) \<le> i" 
        by (simp add: adc_def)
    }
    thus ?thesis 
      using \<open>0 < w \<Longrightarrow> real (bits_to_nat (adc w i)) \<le> i\<close> by blast
qed

(*theorem n_zero_adc_helper_not_greater_than_i: 
  assumes " i \<ge> 0"
  assumes "n = 0" 
  assumes "bits_to_nat(r1 @ clone n False) \<le> i"
  assumes "(l1, l2) = adc_step i (r1, clone n False)"
  shows "real(bits_to_nat(l1 @ l2)) \<le> i" 
 
proof- 
   have "bits_to_nat(r1 @ []) \<le> i" 
     using assms(2) assms(3) by auto
   then have "bits_to_nat(r1) \<le> i"
     by simp
   moreover have "(l1, l2) = adc_step i (r1, [])" 
     using assms(2) assms(4) by auto 
   then have "l2 = []" 
     by simp
    then have "l1 = r1 @ [(real(bits_to_nat(r1 @ [True])) \<le> i)]" 
      using \<open>(l1, l2) = adc_step (real i) (r1, [])\<close> by auto
    then have "real(bits_to_nat(l1)) \<le> i " try

qed : Don't need to prove as n=0 is exit condition of adc_helper*)




(*section \<open> Task 5: Fermat's Last Theorem. \<close>

text \<open> This is (a version of) Fermat's right-triangle theorem. (In fact, it is believed to 
       be the only one of his theorems for which his original complete proof survives.) The
       theorem says that if we have an integer-sided right triangle with hypotenuse c and 
       other sides d and e (i.e. d^2 + e^2 = c^2 by Pythagoras), then d and e cannot both 
       be squares (i.e. there do not exist integers a and b such that d = a^2 and e = b^2). 
       It can be stated more concisely as follows: if a, b, and c are all positive integers, 
       then a^4 + b^4 \<noteq> c^2. Without loss of generality, we can assume that
       any such triangle is in a "reduced" form by removing any common factors between a and
       b (i.e. that the GCD of a and b is 1), and we can also assume that a is odd (at least
       one of a and b have to be odd, otherwise they'd have a common factor of 2, so it might 
       as well be a). \<close>

lemma fermat_right_triangle:
  "\<And>a b c::nat. \<lbrakk> a*b*c > 0; odd a; gcd a b = 1 \<rbrakk> \<Longrightarrow> a^4 + b^4 \<noteq> c^2"
  sorry (* You can assume this theorem is true. No need to prove it! *)

text \<open> Your task is to prove Fermat's Last Theorem in the special case where the exponent is 4. 
       The theorem states that if x, y, and z are all positive integers, then x^4 + y^4 is 
       never equal to z^4. You are advised to use the lemma above to help you! \<close>

theorem fermat4: 
  "\<And>x y z::nat. x*y*z > 0 \<Longrightarrow> x^4 + y^4 \<noteq> z^4"
  oops

end*)
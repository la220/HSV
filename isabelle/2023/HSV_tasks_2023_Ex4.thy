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
theorem
  assumes "0 \<le> i"
  shows "real (bits_to_nat (adc w i)) \<le> i"
proof (auto)
qed
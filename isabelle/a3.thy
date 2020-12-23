theory a3
imports 
  AutoCorres.AutoCorres "HOL-Number_Theory.Number_Theory"
begin

(*---------------------------------------------------------*)
(*---------------------------------------------------------*)

(* Installing the C file and converting it using the AutoCorress tool *)

install_C_file "dlist.c"

autocorres [unsigned_word_abs=is_prime_2, ts_force nondet=is_prime_2] "dlist.c"

term "is_valid_node_C p"


(* Definition of *path*: (path vld hp nxt p l q) says that you start 
   from pointer p, and "follow" the function nxt, adding each encountered 
   pointer to the list l, until you reach the pointer q, and that 
   all encountered pointers are valid nodes according to the predicate vld, 
   are not NULL, and not q:
      l=[ p ,  p1 , p2 , q    ]
          \<down>    \<down>    \<down>    \<down>
          []\<longrightarrow>[]\<longrightarrow>[]\<longrightarrow>[]
            nxt  nxt  nxt 
*)
  
primrec
  path :: "(node_C ptr \<Rightarrow> bool) \<Rightarrow>    \<comment>\<open> valid predicate \<close>
              (node_C ptr \<Rightarrow> node_C) \<Rightarrow>  \<comment>\<open> the heap \<close>
              (node_C \<Rightarrow> node_C ptr) \<Rightarrow>  \<comment>\<open> the function that maps to next element, 
                                            i.e. the field of the node \<close>
               node_C ptr \<Rightarrow>             \<comment>\<open> the starting pointer \<close>
               node_C ptr list \<Rightarrow>        \<comment>\<open> the list of traversed pointers \<close>
               node_C ptr \<Rightarrow>             \<comment>\<open> the end pointer \<close>
               bool"
where
  "path vld hp nxt p [] q = (p = q)"
| "path vld hp nxt p (x#xs) q = (p \<noteq> q \<and> vld p \<and> p \<noteq> NULL \<and> p=x \<and> 
                                path vld hp nxt (nxt (hp p)) xs q)"

print_theorems

(* Definition of *is_dlist*: (is_dlist vld hp p q xs) is True if we 
   have a valid doubly-linked list starting from p and ending in q:
        xs=[ p , p1, p2, q ]
             \<down>   \<down>   \<down>   \<down>
       NULL\<leftarrow>[]\<rightleftharpoons>[]\<rightleftharpoons>[]\<rightleftharpoons>[]\<rightarrow> NULL
*)   


definition
  "is_dlist vld hp p xs q \<equiv> 
  path vld hp next_C p xs NULL \<and> path vld hp prev_C q (rev xs) NULL"

print_theorems

(* (a) Start proof of insert_after_inserts *)

(* TODO: start the proof in question (d) below, just to give you 
   a feeling of what the goal looks like and why we need
   all the helper lemmas *)


(* (b) Prove path_upd *)

find_theorems fun_upd

lemma path_upd[simp]:
  "x \<notin> set xs \<Longrightarrow> path vld (hp (x := y)) n p xs q = path vld hp n p xs q"
  apply (induct xs arbitrary:p)
  sorry
 

(* (c) Prove path_in, path_unique, path_appendD, path_hd_not_in_tl,
       path_append_last *)

lemma path_is_null[simp]:
  "path vld hp n NULL xs q = (xs = [] \<and> q = NULL)"
  by (cases xs; clarsimp; blast)

lemma path_not_null:
  "p \<noteq> NULL \<Longrightarrow> path vld hp n p xs q = (xs = [] \<and> q = p \<or> (\<exists>ys. vld p \<and> p \<noteq> q \<and> xs = p#ys \<and> path vld hp n (n (hp p)) ys q))"
  by (cases xs; clarsimp; blast)

lemma path_in:
  "\<lbrakk>path vld hp n p xs q; xs \<noteq> []\<rbrakk> \<Longrightarrow> p \<in> set xs"
  by (cases xs; simp)

lemma path_unique[simp]:
  "\<lbrakk> path vld hp n p xs q; path vld hp n p ys q \<rbrakk> \<Longrightarrow> xs = ys"
  apply (induct xs arbitrary:p ys; clarsimp)
   apply (metis path_is_null path_not_null)
  apply (simp add:path_not_null)
  by blast

lemma path_appendD[simp]:
  "path vld hp n p (xs@ys) q \<Longrightarrow>
   \<exists>r. path vld hp n p xs r \<and>  path vld hp n r ys q"
  apply (induct xs arbitrary:p; simp)
  by (metis append_Cons path.simps(2) path_unique self_append_conv2)

lemma path_hd_not_in_tl:
  "path vld hp n (n (hp p)) xs q \<Longrightarrow> p \<notin> set xs"
  apply (clarsimp simp:in_set_conv_decomp)
  apply (frule path_appendD)
  by (fastforce dest:path_unique)

lemma path_append_last[simp]:
  "path vld hp n p (xs@ys) q = 
  (path vld hp n p xs (if ys = [] then q else hd ys) \<and> 
   path vld hp n (if ys = [] then q else hd ys) ys q \<and> set xs \<inter> set ys = {} \<and> q \<notin> set xs)"
  apply (induct xs arbitrary:p; clarsimp)
   apply (metis (full_types) list.sel(1) path_is_null path_not_null)
  apply (rule conjI)
   apply (rule impI)
   apply auto[1]
  apply (rule impI)
proof -
  fix x1 :: "node_C ptr" and xsa :: "node_C ptr list" and pa :: "node_C ptr"
assume a1: "\<And>p. path vld hp n p (xsa @ ys) q = (path vld hp n p xsa (if ys = [] then q else hd ys) \<and> path vld hp n (if ys = [] then q else hd ys) ys q \<and> set xsa \<inter> set ys = {} \<and> q \<notin> set xsa)"
assume a2: "ys \<noteq> []"
moreover
  { assume "pa \<in> set ys"
moreover
  { assume "\<exists>p. (ys \<noteq> [] \<and> path vld hp n (n (hp p)) xsa (hd ys)) \<and> p \<in> set (xsa @ ys)"
    then have "\<exists>p. (ys \<noteq> [] \<and> \<not> path vld hp n p (xsa @ ys) q) \<and> path vld hp n p xsa (hd ys)"
      by (meson path_hd_not_in_tl)
      then have "(pa \<noteq> q \<and> vld pa \<and> pa \<noteq> NULL \<and> pa = x1 \<and> path vld hp n (n (hp pa)) xsa (hd ys) \<and> path vld hp n (hd ys) ys q \<and> set xsa \<inter> set ys = {} \<and> q \<notin> set xsa) = (pa \<noteq> hd ys \<and> vld pa \<and> pa \<noteq> NULL \<and> pa = x1 \<and> path vld hp n (n (hp pa)) xsa (hd ys) \<and> path vld hp n (hd ys) ys q \<and> x1 \<notin> set ys \<and> set xsa \<inter> set ys = {} \<and> q \<noteq> x1 \<and> q \<notin> set xsa)"
        using a1 by fastforce }
ultimately have "(pa \<noteq> q \<and> vld pa \<and> pa \<noteq> NULL \<and> pa = x1 \<and> path vld hp n (n (hp pa)) xsa (hd ys) \<and> path vld hp n (hd ys) ys q \<and> set xsa \<inter> set ys = {} \<and> q \<notin> set xsa) = (pa \<noteq> hd ys \<and> vld pa \<and> pa \<noteq> NULL \<and> pa = x1 \<and> path vld hp n (n (hp pa)) xsa (hd ys) \<and> path vld hp n (hd ys) ys q \<and> x1 \<notin> set ys \<and> set xsa \<inter> set ys = {} \<and> q \<noteq> x1 \<and> q \<notin> set xsa)"
  using a2 by auto }
  ultimately show "(pa \<noteq> q \<and> vld pa \<and> pa \<noteq> NULL \<and> pa = x1 \<and> path vld hp n (n (hp pa)) xsa (hd ys) \<and> path vld hp n (hd ys) ys q \<and> set xsa \<inter> set ys = {} \<and> q \<notin> set xsa) = (pa \<noteq> hd ys \<and> vld pa \<and> pa \<noteq> NULL \<and> pa = x1 \<and> path vld hp n (n (hp pa)) xsa (hd ys) \<and> path vld hp n (hd ys) ys q \<and> x1 \<notin> set ys \<and> set xsa \<inter> set ys = {} \<and> q \<noteq> x1 \<and> q \<notin> set xsa)"
    by fastforce
qed

(* (d) Finish proof of correctness insert_after_inserts *)

definition insert_pre
where
  "insert_pre p xs q nd s= 
    (xs\<noteq>[] \<and> is_dlist (is_valid_node_C s) (heap_node_C s) p xs q \<and>  
    nd \<noteq> NULL \<and> is_valid_node_C s nd \<and>  nd \<notin> set xs )"

definition insert_post
where
  "insert_post p xs nd s= 
    is_dlist (is_valid_node_C s) (heap_node_C s) p (xs @ [nd]) nd "

context dlist
begin

find_theorems dlist

find_theorems  hoare_weaken_pre

lemma insert_after_inserts:
  "\<lbrace>\<lambda> s. insert_pre p xs q nd s\<rbrace>
     insert_after' nd q
   \<lbrace>\<lambda>_ s. insert_post p xs nd s\<rbrace>"
  apply (unfold insert_after'_def)
  apply (unfold insert_pre_def)
  apply (unfold insert_post_def)
  apply (unfold is_dlist_def)
  apply wp
  apply (simp)
  apply safe
  using path_in apply fastforce
         apply (erule notE)
         apply (simp)
        apply (erule notE)
        apply (cases "rev xs")
         apply blast
        apply simp
       apply (cases "rev xs")
        apply blast
       apply simp
       apply (cases "rev xs")
       apply blast
      apply simp
       apply (cases "rev xs")
      apply blast
     apply simp
       apply (cases "rev xs")
     apply blast
    apply simp
       apply (cases "rev xs")
    apply blast
   apply simp
  apply (cases "rev xs")
   apply blast
    apply simp

  by blast

end 

(*---------------------------------------------------------*)
(*---------------------------------------------------------*)

context dlist begin

thm is_prime_2'_def

(* Q2 a): Loop invariant for "is_prime_2". *)
definition
  is_prime_inv :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "is_prime_inv i n \<equiv>
     n \<ge> 2 \<and> n mod 2 \<noteq> 0 \<and> n \<le> UINT_MAX \<and> i \<le> n \<and> i \<ge> 3 \<and> i \<le> UINT_MAX \<and> i mod 2 = 1 \<and> (\<forall>z. z \<ge> 1 \<longrightarrow> z \<le> i \<longrightarrow> n mod z = 0 \<longrightarrow> z = 1 \<or> z = i)" (*TODO*)

(* Q2 b): Measure function for "is_prime_2". Must be strictly decreasing
 * for each loop iteration. *)
definition
  is_prime_measure :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "is_prime_measure i n \<equiv> n - i" (*TODO*)

find_theorems prime

(* Q2 c1): A prime is either 2 or an odd number *)
lemma prime_2_or_odd: "prime n \<Longrightarrow> n = 2 \<or> n mod 2 = Suc 0"
  apply (cases n; clarsimp)
  by (metis even_Suc nat.inject numeral_2_eq_2 primes_dvd_imp_eq two_is_prime_nat)

(* Q2 c2): The loop invariant holds coming into the loop. *)
lemma is_prime_precond_implies_inv: 
  assumes
    "n \<ge> 2"
    "n mod 2 \<noteq> 0"
    "i = 3"
    "n \<le> UINT_MAX"
  shows
  "is_prime_inv i n"
  apply (insert assms)
  apply (unfold is_prime_inv_def)
  apply (rule conjI; simp)
  apply (rule conjI)
   apply (simp add: le_mod_geq)
  apply (rule conjI)
  using UINT_MAX_def apply linarith
  by (metis le_SucE le_antisym numeral_2_eq_2 numeral_3_eq_3)
 
lemma bigger_mod_unequal:
  " i \<le> (n :: nat) \<Longrightarrow> 0 \<noteq> n mod (i :: nat) \<Longrightarrow> i \<noteq> n"
  by auto

(* Q2 c3): The loop invariant holds for each loop iteration. *)
lemma is_prime_body_obeys_inv:
  "is_prime_inv i n \<and> n mod i \<noteq> 0 \<Longrightarrow> is_prime_inv (i + 2) n"
  apply (unfold is_prime_inv_def)
  apply simp
  apply (erule conjE)+
  apply simp
  apply (rule conjI)
   apply (metis Suc_leI dlist.bigger_mod_unequal le_eq_less_or_eq le_nat_shrink_left less_numeral_extra(3) mod_Suc_eq numeral_2_eq_2)
  apply (rule conjI)
   apply (smt Suc_leI le_neq_implies_less less_trans_Suc mod2_Suc_Suc mod_Suc_eq mod_self nat_mod_lem neq0_conv)
  apply (rule allI)
  apply (rule impI)+
  apply clarsimp
  by (metis One_nat_def Suc_1 Suc_leI Suc_n_not_le_n dvd_0_right dvd_imp_mod_0 dvd_trans even_mod_2_iff le_antisym le_neq_implies_less mod_Suc_eq mod_self nat_le_linear)

(* Q2 c4): The loop measure decrements each loop iteration. *)
lemma is_prime_body_obeys_measure:
  "\<lbrakk> is_prime_inv i n; n mod i \<noteq> 0 \<rbrakk>
      \<Longrightarrow> is_prime_measure i n > is_prime_measure (i + 2) n"
  apply (unfold is_prime_inv_def)
  apply (erule conjE)+
  apply (unfold is_prime_measure_def)
  by (metis diff_less_mono2 le_less less_add_same_cancel1 mod_self nat.simps(3) neq0_conv numeral_2_eq_2)

lemma trivial_prime_body:
  "is_prime_inv i n \<Longrightarrow> n mod i \<noteq> 0 \<Longrightarrow> is_prime_inv i n \<and> n mod i \<noteq> 0"
  by auto

(* Q2 c5): The loop invariant implies there is no overflow. *)
lemma is_prime_body_implies_no_overflow:
  "\<lbrakk> is_prime_inv i n; n mod i \<noteq> 0\<rbrakk> \<Longrightarrow> i + 2 \<le> UINT_MAX"
  apply (drule trivial_prime_body)
   apply simp
  apply (drule is_prime_body_obeys_inv)
  apply (unfold is_prime_inv_def)
  by simp

thm prime_nat_iff prime_nat_naiveI

(* Q2 c6): The loop invariant implies the post-condition. *)
lemma is_prime_inv_implies_postcondition:
   "is_prime_inv i n \<Longrightarrow> 0 = n mod i \<Longrightarrow> (if i = n then 1 else 0) = (if prime n then 1 else 0)"
  apply (cases "i = n"; clarsimp)
   apply (unfold is_prime_inv_def)
   apply (erule notE)
   apply (erule conjE)+
   prefer 2
   apply (simp add: prime_nat_not_dvd)
   apply simp_all
  by (metis One_nat_def Suc_leD Suc_leI Suc_le_lessD dvd_imp_mod_0 dvd_nat_bounds numeral_2_eq_2 numeral_3_eq_3 prime_nat_naiveI) 
  
(*
 * Q2 d): Show that "is_prime' n" is correct.
 *
 * AutoCorres has applied "word abstraction" to this function,
 * meaning that you are able to reason using "nats" instead of
 * "word32" data types, at the price of having to reason that
 * your values don't overflow UINT_MAX.
 *)
lemma is_prime_correct:
  "\<lbrace>\<lambda>s. n \<le> UINT_MAX \<rbrace> is_prime_2' n \<lbrace>\<lambda>r s. r = (if prime n then 1 else 0) \<rbrace>!"
  (* Unfold the program body. *)
  apply (unfold is_prime_2'_def)
  (* Annotate the loop with an invariant and measure. *)
  apply (subst whileLoop_add_inv [where
     I="\<lambda>i s. is_prime_inv i n" and
     M="\<lambda>(i, s). is_prime_measure i n" ])

  (*
   * Run "wp" to generate verification conditions.
   *
   * The resulting subgoals are:
   *    1. The loop body obeys the invariant, causes the measure to decrease, and
            does not lead to overflow;
   *    2. The invariant implies the post-condition of the function; and
   *    3. The pre-condition of the function implies the invariant.
   *
   *)
  apply wp
    prefer 3
    apply (cases "n < 2"; clarsimp)
     apply (simp add: leD prime_ge_2_nat)
    apply (rule conjI; safe)
  using dlist.prime_2_or_odd apply blast
  apply (simp add: dlist.is_prime_precond_implies_inv)
  apply (simp add: dlist.is_prime_precond_implies_inv)
   apply (erule conjE)+
   apply (rule conjI)+
  using is_prime_body_obeys_inv apply auto[1]
  using is_prime_body_obeys_measure apply auto[1]
  using is_prime_body_implies_no_overflow apply auto[1]
  by (simp add: dlist.is_prime_inv_implies_postcondition)

end

end 

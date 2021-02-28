theory STLC
imports Main
begin

datatype ty
  = IntT
  | BoolT
  | ArrowT ty ty (infixr "\<rightarrow>" 200)

datatype const
  = IntC int
  | BoolC bool

datatype opr
  = Succ
  | Prev
  | IsZero

types name = nat

datatype stmt
  = SLet name expr stmt
  | SRet expr
  | SCall name expr expr stmt
  | STailCall expr expr 

and expr 
  = Var name
  | Const const
  | PrimApp opr expr
  | Lam nat ty stmt

datatype val
  = VConst const
  | Closure nat ty stmt "(nat \<times> val) list"

section "Option Monad"

definition
  option_bind :: "['a option, 'a => 'b option] => 'b option" where
  "option_bind m f = (case m of None => None | Some r => f r)"
declare option_bind_def[simp]

syntax "_option_bind" :: "[pttrns,'a option,'b] => 'c" ("(_ := _;//_)" 0)
translations "P := E; F" == "CONST option_bind E (%P. F)"

definition return :: "'a \<Rightarrow> 'a option" where
  "return x \<equiv> Some x"
declare return_def[simp]
definition error :: "'a option" where
  "error \<equiv> None"
declare error_def[simp]

section "Operational Semantics"

types env = "(nat \<times> val) list"
types stack = "(stmt \<times> env) list"
types state = "stmt \<times> env \<times> stack"

fun lookup :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b option" where
  "lookup x [] = None" |
  "lookup x ((y,v)#bs) = (if x = y then Some v else lookup x bs)"

fun delta :: "opr \<Rightarrow> val \<Rightarrow> val option" where
  "delta Succ (VConst (IntC n)) = Some (VConst (IntC (n + 1)))" |
  "delta Prev (VConst (IntC n)) = Some (VConst (IntC (n - 1)))" |
  "delta IsZero (VConst (IntC n)) = Some (VConst (BoolC (n = 0)))" |
  "delta f v = None"

fun eval :: "expr \<Rightarrow> env \<Rightarrow> val option" where
  "eval (Var x) \<rho> = lookup x \<rho>" |
  "eval (Const c) \<rho> = return (VConst c)" |
  "eval (PrimApp f e) \<rho> = (v := eval e \<rho>; delta f v)" |
  "eval (Lam x T s) \<rho> = return (Closure x T s \<rho>)"

fun step :: "state \<Rightarrow> state option" where
  "step (SLet x e s, \<rho>, k) =
    (v := eval e \<rho>; 
     return (s, (x,v)#\<rho> , k))" |
  "step (SRet e, \<rho>, (SCall x e1 e2 s, \<rho>')#k) =
      (v := eval e \<rho>;
       return (s, (x,v)#\<rho>', k))" |
  "step (SCall x e1 e2 s, \<rho>, k) =
     (v1 := eval e1 \<rho>; v2 := eval e2 \<rho>;
      case v1 of
        Closure y T s' \<rho>' \<Rightarrow>
          return (s', (y,v2)#\<rho>', (SCall x e1 e2 s,\<rho>)#k)
      | _ \<Rightarrow> error)" |
  "step (STailCall e1 e2, \<rho>, k) =
     (v1 := eval e1 \<rho>; v2 := eval e2 \<rho>;
      case v1 of
        Closure y T s' \<rho>' \<Rightarrow>
          return (s', (y,v2)#\<rho>', k)
      | _ \<Rightarrow> error)" |
  "step s = None"

datatype result = Fun | Con const | Error | TimeOut

primrec observe :: "val \<Rightarrow> result" where
  "observe (VConst c) = Con c" |
  "observe (Closure x T s \<rho>) = Fun"

definition final :: "state \<Rightarrow> bool" where
  "final s \<equiv> (case s of (SRet e, \<rho>, []) \<Rightarrow> True | _ \<Rightarrow> False)"
declare final_def[simp]

fun steps :: "nat \<Rightarrow> state \<Rightarrow> result" where
  "steps 0 s = TimeOut" |
  "steps (Suc n) (SRet e, \<rho>, []) =
            (case eval e \<rho> of
               None \<Rightarrow> Error
            | Some v \<Rightarrow> observe v)" |
  "steps (Suc n) s =
         (case step s of
           None \<Rightarrow> Error
         | Some s' \<Rightarrow> steps n s')"

definition run :: "stmt \<Rightarrow> result" where
  "run s \<equiv> steps 1000000 (s,[],[])"

types ty_env = "(name \<times> ty) list"

primrec typeof :: "const \<Rightarrow> ty" where
  "typeof (IntC n) = IntT" |
  "typeof (BoolC b) = BoolT"

primrec typeof_opr :: "opr \<Rightarrow> ty" where
  "typeof_opr Succ = (IntT \<rightarrow> IntT)" |
  "typeof_opr Prev = (IntT \<rightarrow> IntT)" |
  "typeof_opr IsZero = (IntT \<rightarrow> BoolT)"

inductive
  wt_expr :: "ty_env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile>\<^isub>e _ : _" [60,60,60] 59) 
  and wt_stmt :: "ty_env \<Rightarrow> stmt \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile>\<^isub>s _ : _" [60,60,60] 59) 
  where
  "lookup x \<Gamma> = Some A \<Longrightarrow> \<Gamma> \<turnstile>\<^isub>e Var x : A" |
  "\<Gamma> \<turnstile>\<^isub>e Const c : typeof c" |
  "\<lbrakk> typeof_opr f = A \<rightarrow> B; \<Gamma> \<turnstile>\<^isub>e e : A \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^isub>e PrimApp f e : B" |
  "\<lbrakk> (x,A)#\<Gamma> \<turnstile>\<^isub>s s : B \<rbrakk> \<Longrightarrow>
     \<Gamma> \<turnstile>\<^isub>e Lam x A s : (A \<rightarrow> B)" |

  "\<lbrakk> \<Gamma> \<turnstile>\<^isub>e e : A; (x,A)#\<Gamma> \<turnstile>\<^isub>s s : B \<rbrakk> \<Longrightarrow>
     \<Gamma> \<turnstile>\<^isub>s SLet x e s : B" |
  "\<lbrakk> \<Gamma> \<turnstile>\<^isub>e e : A \<rbrakk> \<Longrightarrow>
     \<Gamma> \<turnstile>\<^isub>s SRet e : A" |
  "\<lbrakk> \<Gamma> \<turnstile>\<^isub>e e1 : A \<rightarrow> B; \<Gamma> \<turnstile>\<^isub>e e2 : A; (x,B)#\<Gamma> \<turnstile>\<^isub>s s : C \<rbrakk> \<Longrightarrow>
     \<Gamma> \<turnstile>\<^isub>s SCall x e1 e2 s : C" |
  "\<lbrakk> \<Gamma> \<turnstile>\<^isub>e e1 : A \<rightarrow> B; \<Gamma> \<turnstile>\<^isub>e e2 : A \<rbrakk> \<Longrightarrow>
     \<Gamma> \<turnstile>\<^isub>s STailCall e1 e2 : B"

thm wt_expr_wt_stmt.induct

inductive wt_val :: "val \<Rightarrow> ty \<Rightarrow> bool" 
  and wt_env :: "ty_env \<Rightarrow> env \<Rightarrow> bool" ("_ \<turnstile> _" [60,60] 59) where
  wt_vc[intro!]: "typeof c = A \<Longrightarrow> wt_val (VConst c) A" |
  wt_cl[intro!]: "\<lbrakk> \<Gamma> \<turnstile> E; (x,A)#\<Gamma> \<turnstile>\<^isub>s s : B \<rbrakk> \<Longrightarrow> 
     wt_val (Closure x A s E) (A \<rightarrow> B)" |

  wt_nil[intro!]: "[] \<turnstile> []" |
  wt_cons[intro!]: "\<lbrakk> wt_val v A; \<Gamma> \<turnstile> E \<rbrakk> \<Longrightarrow> ((x,A)#\<Gamma>) \<turnstile> ((x,v)#E)"

inductive wt_stack :: "stack \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ : _ \<Rightarrow> _") where
  nil_stack[intro!]: "[] : A \<Rightarrow> A" |
  cons_stack[intro!]: "\<lbrakk> \<Gamma> \<turnstile> \<rho>; (x,A)#\<Gamma> \<turnstile>\<^isub>s s : B; k : B \<Rightarrow> C \<rbrakk> \<Longrightarrow>
      (SCall x e1 e2 s,\<rho>)#k : A \<Rightarrow> C"

inductive wt_state :: "state \<Rightarrow> ty \<Rightarrow> bool" where
  wts[intro!]: "\<lbrakk> \<Gamma> \<turnstile> \<rho>; \<Gamma> \<turnstile>\<^isub>s s : A; k : A \<Rightarrow> B \<rbrakk> \<Longrightarrow>
    wt_state (s, \<rho>, k) B"

fun wt_result :: "result \<Rightarrow> ty \<Rightarrow> bool" where
  "wt_result Fun (A \<rightarrow> B) = True" |
  "wt_result (Con c) T = (typeof c = T)" |
  "wt_result Error T = False"

lemma delta_safe: 
  assumes wtop: "typeof_opr f = A \<rightarrow> B"
  and wtv: "wt_val v A"
  shows "\<exists> v'. delta f v = Some v' \<and> wt_val v' B"
  sorry

lemma lookup_safe: 
  assumes wtg: "\<Gamma> \<turnstile> \<rho>" and l: "lookup x \<Gamma> = Some A"
  shows "\<exists> v. lookup x \<rho> = Some v \<and> wt_val v A"
  sorry

lemma eval_safe:
  assumes wte: "\<Gamma> \<turnstile>\<^isub>e e : A"
  and wtg: "\<Gamma> \<turnstile> \<rho>"
  shows "\<exists> v. eval e \<rho> = Some v \<and> wt_val v A"
  sorry

lemma step_safe: 
  assumes wtsA: "wt_state s A"
  shows "final s \<or> (\<exists> s'. step s = Some s' \<and> wt_state s' A)"
  sorry

lemma steps_safe:
  assumes wtsA: "wt_state s A"
  shows "steps n s = TimeOut \<or> (\<exists> r. steps n s = r \<and> wt_result r A)"
  using wtsA apply (induct n s rule: steps.induct)

theorem type_safety:
  assumes wts: "[] \<turnstile>\<^isub>s s : A"
  shows "\<exists> r. run s = r \<and> (r = TimeOut \<or> wt_result r A)"
proof -
  from wts have 1: "wt_state (s,[],[]) A" by auto
  let ?n = "1000000" and ?s = "(s,[],[])"
  from 1 have 2:
    "steps ?n ?s = TimeOut \<or> (\<exists> r. steps ?n ?s = r \<and> wt_result r A)"
    by (rule steps_safe)
  moreover { assume "steps ?n ?s = TimeOut"
    with 2 have "\<exists> r. run s = r \<and> (r = TimeOut \<or> wt_result r A)"
      by (auto simp: run_def)
  } moreover { assume 3: "\<exists> r. steps ?n ?s = r \<and> wt_result r A"
    from 3 obtain r where 4: "steps ?n ?s = r" and 5: "wt_result r A" by blast
    from 4 have 6: "run s = r" by (simp add: run_def)
    from 6 5 have "\<exists> r. run s = r \<and> (r = TimeOut \<or> wt_result r A)" by blast
  } ultimately show ?thesis by blast
qed

end

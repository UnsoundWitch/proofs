theory stlc               
  imports Main                          
begin                
                                  
datatype ty = TyArw ty ty | TyBool | TyNat
                                                       
type_synonym id = nat

type_synonym 'a alist = "(nat \<times> 'a) list"

fun lookup :: "id \<Rightarrow> 'a alist \<Rightarrow> 'a option" where
  "lookup i [] = None"
| "lookup i ((x, t)#xs) =
    (if i = x then
       Some t
     else
       lookup i xs)"

datatype op = Plus | Mult | Eq

datatype tm =
  TmBool bool | TmNat nat 
  | TmIf tm tm tm | TmOp op tm tm
  | TmVar id | TmApp tm tm | TmAbs id ty tm 
  | TmLet id tm tm

datatype val = BoolV bool | IntV nat | FunV id tm
                                   
inductive is_val where
  v_abs : "is_val (TmAbs x T t)" 
| v_nat : "is_val (TmNat n)" 
| v_bool : "is_val (TmBool b)"          

print_theorems

primrec op_type :: "op \<Rightarrow> ty" where
  "op_type Plus = TyNat"
| "op_type Mult = TyNat"
| "op_type Eq = TyBool"

type_synonym ctx = "ty alist"

inductive has_type :: "ctx \<Rightarrow> tm \<Rightarrow> ty \<Rightarrow> bool" where
  T_Bool : "has_type _ (TmBool _) TyBool" 
| T_Nat : "has_type _ (TmNat _) TyNat"
| T_If : "has_type \<Gamma> e1 TyBool \<Longrightarrow>
          has_type \<Gamma> e2 T \<Longrightarrow>
          has_type \<Gamma> e3 T \<Longrightarrow>
          has_type \<Gamma> (TmIf e1 e2 e3) T"
| T_Op : "T = op_type op \<Longrightarrow>
          has_type \<Gamma> e1 T \<Longrightarrow>
          has_type \<Gamma> e2 T \<Longrightarrow>
          has_type \<Gamma> (TmOp op e1 e2) T"
| T_Var : "Some T = lookup i \<Gamma> \<Longrightarrow> has_type \<Gamma> (TmVar i) T"
| T_App : "has_type \<Gamma> e2 T1 \<Longrightarrow> has_type \<Gamma> e1 (TyArw T1 T2) \<Longrightarrow> has_type \<Gamma> (TmApp e1 e2) T2"
| T_Abs : "has_type ((i, T1)#\<Gamma>) e T2 \<Longrightarrow>
           has_type \<Gamma> (TmAbs i T1 e) (TyArw T1 T2)"
| T_Let : "has_type \<Gamma> e1 T1 \<Longrightarrow>
           has_type ((i, T1)#\<Gamma>) e2 T2 \<Longrightarrow> has_type \<Gamma> (TLet i e1 e2) T2"

print_theorems

primrec subst :: "id \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm" where
  "subst _ _ (TmBool b) = (TmBool b)"
| "subst _ _ (TmNat n) = (TmNat n)"
| "subst x s (TmIf e1 e2 e3) = (TmIf (subst x s e1) (subst x s e2) (subst x s e3))"
| "subst x s (TmOp op e1 e2) = (TmOp op (subst x s e1) (subst x s e2))"
| "subst x s (TmVar i) = (if i = x then s else (TmVar i))"
| "subst x s (TmApp e1 e2) = (TmApp (subst x s e1) (subst x s e2))"
| "subst x s (TmAbs i ty e) = (if i = x then (TmAbs i ty e) else (TmAbs i ty (subst x s e)))"
| "subst x s (TmLet i e1 e2) = 
              (if i = x 
               then (TmLet i (subst x s e1) e2) 
               else (TmLet i (subst x s e1) (subst x s e2)))"

fun step_op :: "op \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm" where
  "step_op Plus (TmNat i) (TmNat j) = TmNat (i + j)"
| "step_op Mult (TmNat i) (TmNat j) = TmNat (i * j)"
| "step_op Eq (TmNat i) (TmNat j) = TmBool (i = j)"

inductive step :: "tm \<Rightarrow> tm \<Rightarrow> bool" where
  ST_IfTrue: "step (TmIf (TmBool True) e1 e2) e1"
| ST_IfFalse: "step (TmIf (TmBool False) e1 e2) e2"
| ST_If1: "step e0 e0' \<Longrightarrow> step (TmIf e0 e1 e2) (TmIf e0' e1 e2)"
| ST_Op1: "step e1 e1' \<Longrightarrow> step (TmOp op e1 e2) (TmOp op e1' e2)"
| ST_Op2: "is_val v1 \<Longrightarrow> step e2 e2' \<Longrightarrow> step (TmOp op v1 e2) (TmOp op v1 e2')"
| ST_OpRes: "is_val v1 \<Longrightarrow> is_val v2 \<Longrightarrow> step (TmOp op v1 v2) (step_op op v1 v2)"
| ST_AppAbs: "is_val v \<Longrightarrow> step (TmApp (TmAbs i T e) v) (subst i v e)"
| ST_App1: "step t1 t1' \<Longrightarrow> step (TmApp t1 t2) (TmApp t1' t2)"
| ST_App2: "is_val v1 \<Longrightarrow> step t2 t2' \<Longrightarrow> step (TmApp v1 t2) (TmApp v1 t2')"
| ST_Let1: "step e1 e1' \<Longrightarrow> step (TmLet i e1 e2) (TmLet i e1' e2)"
| ST_Let2: "is_val v1 \<Longrightarrow> step (TmLet i v1 e2) (subst i v1 e2)"
| ST_Trans: "step e1 e2 \<Longrightarrow> step e2 e3 \<Longrightarrow> step e1 e3"

print_theorems

lemma example_1:
  shows "step (TmIf (TmOp Eq (TmNat 0) (TmNat 1)) (TmBool True) (TmBool False)) (TmBool False)"
  apply (rule ST_Trans)
   apply (rule ST_If1)
   apply (rule ST_OpRes; simp add:is_val.simps)
  apply simp
  by (rule ST_IfFalse)

fun inclusion :: "ctx \<Rightarrow> ctx \<Rightarrow> bool" where
  "inclusion [] [] = True"
| "inclusion (x1#xs1) (x2#xs2) =
     (if (x1 = x2) then False else inclusion xs1 xs2)"
| "inclusion (x1#xs1) [] = False"
| "inclusion [] (x2#xs2) = True"

print_theorems


lemma weakening : "has_type \<Gamma>1 t S \<Longrightarrow> inclusion \<Gamma>1 \<Gamma>2 \<Longrightarrow> has_type \<Gamma>2 t S" 
  apply (induct t S arbitrary:\<Gamma>1 rule:has_type.induct)
         apply (simp add:has_type.intros)+
     apply (rule T_Var) 
 
     apply (induct rule:inclusion.induct; auto)

  sorry

lemma context_inv_empty : "has_type [] t S \<Longrightarrow> has_type \<Gamma> t S"
  using inclusion.elims(3) weakening by fastforce 

lemma preservation : "step t t' \<Longrightarrow> has_type [] t T \<Longrightarrow>  has_type [] t' T"
  apply (induct t t' rule:step.induct)
  apply (erule T_If)
  sorry

lemma progress : "\<Gamma> = [] \<Longrightarrow> has_type \<Gamma> t T \<Longrightarrow> value t \<or> (\<exists> t'. step t t')"
  sorry

(*
fun eval_op :: "op \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm option" where
  "eval_op Plus (TmNat i) (TmNat j) = Some (TmNat (i + j))"
| "eval_op Mult (TmNat i) (TmNat j) = Some (TmNat (i * j))"
| "eval_op Eq (TmNat i) (TmNat j) = Some (TmBool (i = j))"
| "eval_op _ _ _ = None"

type_synonym env = "tm alist"

function eval :: "env \<Rightarrow> tm \<Rightarrow> tm option" where
  "eval \<Delta> (TmBool b) = Some (TmBool b)"
| "eval \<Delta> (TmNat n) = Some (TmNat n)"
| "eval \<Delta> (TmIf e1 e2 e3) = 
      (case eval \<Delta> e1 of
        Some (TmBool True) \<Rightarrow> eval \<Delta> e2
        | Some (TmBool False) \<Rightarrow> eval \<Delta> e3
        | _ \<Rightarrow> None)"
| "eval \<Delta> (TmOp op e1 e2) = (
      let e1' = eval \<Delta> e1 in
      let e2' = eval \<Delta> e2 in
      case (e1', e2') of
        (Some arg1, Some arg2) \<Rightarrow> eval_op op arg1 arg2
        | _ \<Rightarrow> None)"
| "eval \<Delta> (TmVar i) = lookup i \<Delta>"
| "eval \<Delta> (TmApp e1 e2) = (
      let e1' = eval \<Delta> e1 in
      let e2' = eval \<Delta> e2 in
      case (e1', e2') of
       (Some (TmAbs i _ e3), Some arg) \<Rightarrow> eval ((i, e2)#\<Delta>) e3
       | _ \<Rightarrow> None)"
| "eval \<Delta> (TmAbs i ty e) = Some (TmAbs i ty e)"
| "eval \<Delta> (TmLet i e1 e2) = (
      case eval \<Delta> e1 of
        Some x \<Rightarrow> eval ((i, x)#\<Delta>) e2
        | _ \<Rightarrow> None)"
                      apply auto
  by (meson tm.exhaust)

termination eval
  apply (rule local.termination)  

print_theorems

lemma example1:
  shows "eval [] (TmBool False) = Some (TmBool False)"
  
  by (simp add:eval.psimps)

lemma example1:
  shows "eval [] (TmIf (TmOp Eq (TmNat 0) (TmNat 1)) (TmBool True) (TmBool False)) = Some (TmBool False)"
  apply (simp add:eval_def)
  by simp
*)

end

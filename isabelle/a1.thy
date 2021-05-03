theory a1
imports Main
begin

(*
  You must use only these proof methods:
   - rule, erule, assumption, cases

  You must use only there proof rules:
   - impI, impE, conjI, conjE, disjI1, disjI2, disjE, notI, notE
     iffI, iffE, iffD1, iffD1, iffD2, ccontr, classical, FalseE,
     TrueI, conjunct1, conjunct2, mp
*)

thm impI impE notI iffD1 iffD2 notE

lemma prop_a:
  "(¬B ⟶ A) = (A ∨ B)"
  apply (rule iffI)
   apply (rule classical)
   apply (erule impE)
    apply (rule notI)
    apply (erule notE)
    apply (rule disjI2)
    apply assumption
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (rule impI)
  apply (erule disjE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma prop_b:
  "(A ⟶ B ⟶ C) = (B ⟶ A ⟶ C)"
  apply (rule iffI)
   apply (rule impI)
   apply (rule impI)
   apply (erule impE)
    apply assumption
   apply (erule impE)
    apply assumption
   apply assumption
  apply (rule impI)
  apply (rule impI)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma prop_c:
  "(P ⟶ Q) = (¬Q ⟶ ¬P)"
  apply (rule iffI)
  apply (rule impI)
   apply (rule notI)
   apply (erule notE)
   apply (erule impE)
    apply assumption
   apply assumption
  apply (rule classical)
   apply (rule impI)
  apply (erule impE)
   apply (rule notI)
   apply (erule notE)
   apply (rule impI)
   apply assumption
  apply (erule notE)
  apply (rule impI)
  apply (erule notE)
  apply assumption
  done

lemma prop_d:
  "((A ∨ B) ∧ C) = (A ∧ C ∨ C ∧ B)"
  apply (rule iffI)
  apply (erule conjE)
   apply (erule disjE)
    apply (rule disjI1)
    apply (rule conjI)
     apply assumption
    apply assumption
   apply (rule disjI2)
   apply (rule conjI)
    apply assumption
   apply assumption
  apply (erule disjE)
   apply (erule conjE)
   apply (rule conjI)
    apply (rule disjI1)
    apply assumption
   apply assumption
  apply (erule conjE)
  apply (rule conjI)
   apply (rule disjI2)
   apply assumption
  apply assumption 
  done

lemma prop_e:
  "((P ⟶ (((Q ⟶ R) ⟶ Q) ⟶ Q)) ⟶ P) ⟶ P"
  apply (rule impI)
  apply (erule impE)
  apply (rule impI)
   apply (rule impI)
  apply (rule classical)
   apply (erule impE)
    apply (rule impI)
    apply (erule notE)
  apply assumption
   apply (erule notE)
   apply assumption
  apply assumption
  done

lemma prop_f:
  "¬ ¬ P ⟹ P"
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma prop_g:
  "(¬A ∧ (B ⟶ C)) = (A ∨ B ⟶ ¬A ∧ C)"
  apply (rule iffI)
   apply (rule impI)
   apply (erule conjE)
   apply (erule disjE)
    apply (erule impE)
     apply (erule notE)
     apply assumption
    apply (erule notE)
    apply assumption
   apply (rule conjI)
    apply (rule notI)
    apply (erule notE)
    apply (erule impE)
     apply assumption
    apply assumption
   apply (erule impE)
    apply assumption
   apply assumption
  apply (rule conjI)
   apply (rule classical)
   apply (erule impE)
  apply (rule disjI1)
  apply (rule classical)
  apply (erule notE)
    apply assumption
   apply (rule notI)
   apply (erule notE)
   apply (erule conjE)
   apply (erule notE)
   apply assumption
  apply (rule impI)
  apply (erule impE)
   apply (rule disjI2)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

(*
You must only these proof methods:
  - rule, erule, assumption, frule, drule,
    rule_tac, erule_tac, frule_tac, drule_tac, rename_tac, case_tac
You must use only these proof rules:
  -  impI, impE, conjI, conjE, disjI1, disjI2, disjE, notI, notE,
     iffI, iffE, iffD1, iffD2, ccontr, classical, FalseE, TrueI,
     allI, allE, exI, and exE
*)

thm allE

lemma hol_a:
  "((∀x. P x) ∧ (∀x. Q x)) = (∀x. Q x ∧ P x)"
  apply (rule iffI)
   apply (erule conjE)
   apply (rule allI)
   apply (erule_tac x=x in allE)
   apply (erule_tac x=x in allE)
   apply (rule conjI)
    apply assumption
   apply assumption
  apply (rule conjI)
   apply (rule allI)
   apply (erule_tac x=x in allE)
   apply (erule conjE)
   apply assumption
  apply (rule allI)
  apply (erule_tac x=x in allE)
  apply (erule conjE)
  apply assumption
  done

lemma hol_b:
  "(∀x. P x ⟶ Q) ⟹ (∃x. P x) ⟶ Q"
  apply (rule impI)
  apply (erule_tac exE)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply assumption
  done

lemma hol_c:
  "(¬ (∀ x. P x)) = (∃ x. ¬ P x)"
  apply (rule iffI)
   apply (rule ccontr)
   apply (erule notE)
   apply (rule allI)
   apply (rule ccontr)
  apply (erule notE)
   apply (rule_tac x=x in exI)
  apply assumption
  apply (erule exE)
  apply (rule notI)
  apply (erule notE)
  apply (erule_tac x=x in allE)
  apply assumption
  done

lemma hol_d:
  "(∀a. P a a) ⟶ ¬(∀a b. P b a ⟶ ¬P a b)"
  apply (rule impI)
  apply (rule notI)
  apply (erule_tac x=a in allE)
  apply (erule_tac x=a in allE)
  apply (erule_tac x=a in allE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma hol_e:
  "(∀P x. P x) = False"
  apply (rule iffI)
   apply (erule allE)
   apply (erule allE)
   apply assumption
  apply (rule allI)
  apply (rule allI)
  apply (erule FalseE)
  done

lemma hol_f:
  "∀P h. (∀x. ¬P x ⟶ P (h x)) ⟶ (∃x. P x ∧ P (h (h x)))"
  apply (rule allI)
  apply (rule allI)
  apply (rule impI)
  apply (rule classical)
  apply (erule allE)
  apply (rule exI)
  apply (rule conjI)
   apply (erule notE)
   apply (rule exI)
   apply (rule classical)
  oops

end

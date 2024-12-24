Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247241_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1247222 (_22840 : nat) (_22841 : nat) (m : nat) (n : nat) (p : nat) : (term0 m n p _22841 _22840) = (term1 _22840 _22841 m n p).
Proof. exact (@lem1246844 _22840 _22841 (term2 m n p)). Qed.
Lemma lem1247223 (m : nat) (n : nat) (p : nat) : (term3 n m p) = (term4 m n p).
Proof. exact (@lem1247222 p m m n p). Qed.
Lemma lem1247224 (d : nat) (m : nat) (n : nat) (p : nat) : (term5 m n p d) = (term6 d m n p).
Proof. exact (eq_refl (term5 m n p d)). Qed.
Lemma lem1247225 (p : nat) (m : nat) (d : nat) : (term7 p m d) = (term7 p m d).
Proof. exact (eq_refl (term7 p m d)). Qed.
Lemma lem1247226 (d : nat) (m : nat) (n : nat) (p : nat) : (term8 m n p d) = (term9 d m n p).
Proof. exact (MK_COMB (@lem1247225 p m d) (@lem1247224 d m n p)). Qed.
Lemma lem1247227 (d : nat) (m : nat) (n : nat) (p : nat) : (term5 m n p d) = (term6 d m n p).
Proof. exact (eq_refl (term5 m n p d)). Qed.
Lemma lem1247228 (m : nat) (p : nat) (d : nat) : (term7 m p d) = (term7 m p d).
Proof. exact (eq_refl (term7 m p d)). Qed.
Lemma lem1247229 (d : nat) (m : nat) (n : nat) (p : nat) : (term10 m n p d) = (term11 d m n p).
Proof. exact (MK_COMB (@lem1247228 m p d) (@lem1247227 d m n p)). Qed.
Lemma lem1247230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247231 (d : nat) (m : nat) (n : nat) (p : nat) : (term12 m n p d) = (term13 d m n p).
Proof. exact (MK_COMB (@lem1247230) (@lem1247229 d m n p)). Qed.
Lemma lem1247232 (d : nat) (m : nat) (n : nat) (p : nat) : (term14 m n p d) = (term15 d m n p).
Proof. exact (MK_COMB (@lem1247231 d m n p) (@lem1247226 d m n p)). Qed.
Lemma lem1247233 (m : nat) (n : nat) (p : nat) : (term16 m n p) = (term17 m n p).
Proof. exact (fun_ext (fun d : nat => @lem1247232 d m n p)). Qed.
Lemma lem1247234 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1247235 (m : nat) (n : nat) (p : nat) : (term4 m n p) = (term18 m n p).
Proof. exact (MK_COMB (@lem1247234) (@lem1247233 m n p)). Qed.
Lemma lem1247236 (m : nat) (n : nat) (p : nat) : (term3 n m p) = (term19 m n p).
Proof. exact (eq_refl (term3 n m p)). Qed.
Lemma lem1247237 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247238 (m : nat) (n : nat) (p : nat) : (term20 n m p) = (term21 m n p).
Proof. exact (MK_COMB (@lem1247237) (@lem1247236 m n p)). Qed.
Lemma lem1247239 (m : nat) (n : nat) (p : nat) : ((term3 n m p) = (term4 m n p)) = ((term19 m n p) = (term18 m n p)).
Proof. exact (MK_COMB (@lem1247238 m n p) (@lem1247235 m n p)). Qed.
Lemma lem1247240 (m : nat) (n : nat) (p : nat) : (term19 m n p) = (term18 m n p).
Proof. exact (EQ_MP (@lem1247239 m n p) (@lem1247223 m n p)). Qed.
Lemma lem1247241 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (term19 m n p).
Proof. exact (SYM (@lem1247240 m n p)). Qed.

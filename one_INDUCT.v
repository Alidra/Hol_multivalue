Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import one_INDUCT_term_abbrevs.
Require Import one_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Lemma lem15933 (v : unit) : term0 v.
Proof. exact (@lem15881 v). Qed.
Lemma lem15934 (v : unit) : (term0 v) = (v = tt).
Proof. exact (eq_refl (term0 v)). Qed.
Lemma lem15959 (v : unit) : v = tt.
Proof. exact (EQ_MP (@lem15934 v) (@lem15933 v)). Qed.
Lemma lem15960 : tt = tt.
Proof. exact (@lem15959 tt). Qed.
Lemma lem15961 (P : unit -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem15962 (P : unit -> Prop) : (P tt) = (P tt).
Proof. exact (MK_COMB (@lem15961 P) (@lem15960)). Qed.
Lemma lem15963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem15964 (P : unit -> Prop) : (term1 P) = (term1 P).
Proof. exact (MK_COMB (@lem15963) (@lem15962 P)). Qed.
Lemma lem15980 (v : unit) : v = tt.
Proof. exact (EQ_MP (@lem15934 v) (@lem15933 v)). Qed.
Lemma lem15981 (x : unit) : x = tt.
Proof. exact (@lem15980 x). Qed.
Lemma lem15982 (P : unit -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem15983 (x : unit) (P : unit -> Prop) : (P x) = (P tt).
Proof. exact (MK_COMB (@lem15982 P) (@lem15981 x)). Qed.
Lemma lem15984 (P : unit -> Prop) : (term2 P) = (term3 P).
Proof. exact (fun_ext (fun x : unit => @lem15983 x P)). Qed.
Lemma lem15985 : (@all unit) = (@all unit).
Proof. exact (eq_refl (@all unit)). Qed.
Lemma lem15986 (P : unit -> Prop) : (term4 P) = (term5 P).
Proof. exact (MK_COMB (@lem15985) (@lem15984 P)). Qed.
Lemma lem15987 (P : unit -> Prop) : (term6 P) = (term7 P).
Proof. exact (MK_COMB (@lem15964 P) (@lem15986 P)). Qed.
Lemma lem15988 : term8 = term9.
Proof. exact (fun_ext (fun P : unit -> Prop => @lem15987 P)). Qed.
Lemma lem15989 : (@all (unit -> Prop)) = (@all (unit -> Prop)).
Proof. exact (eq_refl (@all (unit -> Prop))). Qed.
Lemma lem15990 : term10 = term11.
Proof. exact (MK_COMB (@lem15989) (@lem15988)). Qed.
Lemma lem15991 : term11 = term10.
Proof. exact (SYM (@lem15990)). Qed.
Lemma lem15999 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem16000 (t : Prop) : (term13 t) = t.
Proof. exact (@lem15999 unit t). Qed.
Lemma lem16001 (P : unit -> Prop) : (term5 P) = (P tt).
Proof. exact (@lem16000 (P tt)). Qed.
Lemma lem16002 (P : unit -> Prop) : (term1 P) = (term1 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem16003 (P : unit -> Prop) : (term7 P) = (term14 P).
Proof. exact (MK_COMB (@lem16002 P) (@lem16001 P)). Qed.
Lemma lem16005 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem16006 (P : unit -> Prop) : (term14 P) = True.
Proof. exact (@lem16005 (P tt)). Qed.
Lemma lem16007 (P : unit -> Prop) : (term7 P) = True.
Proof. exact (TRANS (@lem16003 P) (@lem16006 P)). Qed.
Lemma lem16008 : term9 = term15.
Proof. exact (fun_ext (fun P : unit -> Prop => @lem16007 P)). Qed.
Lemma lem16009 : (@all (unit -> Prop)) = (@all (unit -> Prop)).
Proof. exact (eq_refl (@all (unit -> Prop))). Qed.
Lemma lem16010 : term11 = term16.
Proof. exact (MK_COMB (@lem16009) (@lem16008)). Qed.
Lemma lem16012 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem16013 (t : Prop) : (term17 t) = t.
Proof. exact (@lem16012 (unit -> Prop) t). Qed.
Lemma lem16014 : term16 = True.
Proof. exact (@lem16013 True). Qed.
Lemma lem16015 : term11 = True.
Proof. exact (TRANS (@lem16010) (@lem16014)). Qed.
Lemma lem16016 : True = term11.
Proof. exact (SYM (@lem16015)). Qed.
Lemma lem16017 : term11.
Proof. exact (EQ_MP (@lem16016) (@lem0)). Qed.
Lemma lem16018 : term10.
Proof. exact (EQ_MP (@lem15991) (@lem16017)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247289_term_abbrevs.
Require Import thm1246844_spec.
Lemma lem1247270 (_22840 : nat) (_22841 : nat) (d : nat) (n : nat) (p : nat) : (term0 d n p _22841 _22840) = (term1 _22840 _22841 d n p).
Proof. exact (@lem1246844 _22840 _22841 (term2 d n p)). Qed.
Lemma lem1247271 (d : nat) (n : nat) (p : nat) : (term3 p d n) = (term4 d n p).
Proof. exact (@lem1247270 n (Nat.add p d) d n p). Qed.
Lemma lem1247272 (d : nat) (d' : nat) (n : nat) (p : nat) : (term5 d n p d') = (term6 d d' n p).
Proof. exact (eq_refl (term5 d n p d')). Qed.
Lemma lem1247273 (n : nat) (p : nat) (d : nat) (d' : nat) : (term7 n p d d') = (term7 n p d d').
Proof. exact (eq_refl (term7 n p d d')). Qed.
Lemma lem1247274 (d : nat) (d' : nat) (n : nat) (p : nat) : (term8 d n p d') = (term9 d d' n p).
Proof. exact (MK_COMB (@lem1247273 n p d d') (@lem1247272 d d' n p)). Qed.
Lemma lem1247275 (d : nat) (d' : nat) (n : nat) (p : nat) : (term5 d n p d') = (term6 d d' n p).
Proof. exact (eq_refl (term5 d n p d')). Qed.
Lemma lem1247276 (p : nat) (d : nat) (n : nat) (d' : nat) : (term10 p d n d') = (term10 p d n d').
Proof. exact (eq_refl (term10 p d n d')). Qed.
Lemma lem1247277 (d : nat) (d' : nat) (n : nat) (p : nat) : (term11 d n p d') = (term12 d d' n p).
Proof. exact (MK_COMB (@lem1247276 p d n d') (@lem1247275 d d' n p)). Qed.
Lemma lem1247278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247279 (d : nat) (d' : nat) (n : nat) (p : nat) : (term13 d n p d') = (term14 d d' n p).
Proof. exact (MK_COMB (@lem1247278) (@lem1247277 d d' n p)). Qed.
Lemma lem1247280 (d : nat) (d' : nat) (n : nat) (p : nat) : (term15 d n p d') = (term16 d d' n p).
Proof. exact (MK_COMB (@lem1247279 d d' n p) (@lem1247274 d d' n p)). Qed.
Lemma lem1247281 (d : nat) (n : nat) (p : nat) : (term17 d n p) = (term18 d n p).
Proof. exact (fun_ext (fun d' : nat => @lem1247280 d d' n p)). Qed.
Lemma lem1247282 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1247283 (d : nat) (n : nat) (p : nat) : (term4 d n p) = (term19 d n p).
Proof. exact (MK_COMB (@lem1247282) (@lem1247281 d n p)). Qed.
Lemma lem1247284 (d : nat) (n : nat) (p : nat) : (term3 p d n) = (term20 d n p).
Proof. exact (eq_refl (term3 p d n)). Qed.
Lemma lem1247285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247286 (d : nat) (n : nat) (p : nat) : (term21 p d n) = (term22 d n p).
Proof. exact (MK_COMB (@lem1247285) (@lem1247284 d n p)). Qed.
Lemma lem1247287 (d : nat) (n : nat) (p : nat) : ((term3 p d n) = (term4 d n p)) = ((term20 d n p) = (term19 d n p)).
Proof. exact (MK_COMB (@lem1247286 d n p) (@lem1247283 d n p)). Qed.
Lemma lem1247288 (d : nat) (n : nat) (p : nat) : (term20 d n p) = (term19 d n p).
Proof. exact (EQ_MP (@lem1247287 d n p) (@lem1247271 d n p)). Qed.
Lemma lem1247289 (d : nat) (n : nat) (p : nat) : (term19 d n p) = (term20 d n p).
Proof. exact (SYM (@lem1247288 d n p)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HREAL_EQ_ADD_LCANCEL_term_abbrevs.
Require Import thm0_spec.
Require Import thm1320494_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem1321285 (x : hreal) : term0 x.
Proof. exact (@lem1320494 x). Qed.
Lemma lem1321286 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1321287 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1321286 x) (@lem1321285 x)). Qed.
Lemma lem1321288 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1321287 x y). Qed.
Lemma lem1321289 (x : hreal) (y : hreal) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1321290 (x : hreal) (y : hreal) : term3 x y.
Proof. exact (EQ_MP (@lem1321289 x y) (@lem1321288 x y)). Qed.
Lemma lem1321291 (x : hreal) (y : hreal) (z : hreal) : term4 x y z.
Proof. exact (@lem1321290 x y z). Qed.
Lemma lem1321292 (x : hreal) (y : hreal) (z : hreal) : (term4 x y z) = (term5 x y z).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem1321293 (x : hreal) (y : hreal) (z : hreal) : term5 x y z.
Proof. exact (EQ_MP (@lem1321292 x y z) (@lem1321291 x y z)). Qed.
Lemma lem1321294 (x : hreal) (y : hreal) (z : hreal) : (term5 x y z) = ((term5 x y z) = True).
Proof. exact (@lem7 (term5 x y z)). Qed.
Lemma lem1321297 (x : hreal) (y : hreal) (z : hreal) : (term5 x y z) = True.
Proof. exact (EQ_MP (@lem1321294 x y z) (@lem1321293 x y z)). Qed.
Lemma lem1321298 (m : hreal) (n : hreal) (p : hreal) : (term5 m n p) = True.
Proof. exact (@lem1321297 m n p). Qed.
Lemma lem1321299 (m : hreal) (n : hreal) (p : hreal) : True = (term5 m n p).
Proof. exact (SYM (@lem1321298 m n p)). Qed.
Lemma lem1321300 (m : hreal) (n : hreal) (p : hreal) : term5 m n p.
Proof. exact (EQ_MP (@lem1321299 m n p) (@lem0)). Qed.
Lemma lem1321311 (n : hreal) (p : hreal) (h1 : n = p) : n = p.
Proof. exact (h1). Qed.
Lemma lem1321312 (m : hreal) (p : hreal) : (term6 m p) = (term6 m p).
Proof. exact (eq_refl (term6 m p)). Qed.
Lemma lem1321313 (m : hreal) (n : hreal) (p : hreal) (h1 : n = p) : (term7 m p n) = (term8 m p).
Proof. exact (MK_COMB (@lem1321312 m p) (@lem1321311 n p h1)). Qed.
Lemma lem1321314 (m : hreal) (p : hreal) : (term8 m p) = ((hreal_add m p) = (hreal_add m p)).
Proof. exact (eq_refl (term8 m p)). Qed.
Lemma lem1321315 (m : hreal) (p : hreal) (n : hreal) : (term9 m p n) = (term9 m p n).
Proof. exact (eq_refl (term9 m p n)). Qed.
Lemma lem1321316 (n : hreal) (m : hreal) (p : hreal) : ((term7 m p n) = (term8 m p)) = ((term7 m p n) = ((hreal_add m p) = (hreal_add m p))).
Proof. exact (MK_COMB (@lem1321315 m p n) (@lem1321314 m p)). Qed.
Lemma lem1321317 (n : hreal) (m : hreal) (p : hreal) : (term7 m p n) = ((hreal_add m n) = (hreal_add m p)).
Proof. exact (eq_refl (term7 m p n)). Qed.
Lemma lem1321318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1321319 (n : hreal) (m : hreal) (p : hreal) : (term9 m p n) = (term10 n m p).
Proof. exact (MK_COMB (@lem1321318) (@lem1321317 n m p)). Qed.
Lemma lem1321320 (m : hreal) (p : hreal) : ((hreal_add m p) = (hreal_add m p)) = ((hreal_add m p) = (hreal_add m p)).
Proof. exact (eq_refl ((hreal_add m p) = (hreal_add m p))). Qed.
Lemma lem1321321 (n : hreal) (m : hreal) (p : hreal) : ((term7 m p n) = ((hreal_add m p) = (hreal_add m p))) = (((hreal_add m n) = (hreal_add m p)) = ((hreal_add m p) = (hreal_add m p))).
Proof. exact (MK_COMB (@lem1321319 n m p) (@lem1321320 m p)). Qed.
Lemma lem1321322 (n : hreal) (m : hreal) (p : hreal) : ((term7 m p n) = (term8 m p)) = (((hreal_add m n) = (hreal_add m p)) = ((hreal_add m p) = (hreal_add m p))).
Proof. exact (TRANS (@lem1321316 n m p) (@lem1321321 n m p)). Qed.
Lemma lem1321323 (m : hreal) (n : hreal) (p : hreal) (h1 : n = p) : ((hreal_add m n) = (hreal_add m p)) = ((hreal_add m p) = (hreal_add m p)).
Proof. exact (EQ_MP (@lem1321322 n m p) (@lem1321313 m n p h1)). Qed.
Lemma lem1321324 (m : hreal) (n : hreal) (p : hreal) (h1 : n = p) : ((hreal_add m p) = (hreal_add m p)) = ((hreal_add m n) = (hreal_add m p)).
Proof. exact (SYM (@lem1321323 m n p h1)). Qed.
Lemma lem1321325 (m : hreal) (p : hreal) : (hreal_add m p) = (hreal_add m p).
Proof. exact (eq_refl (hreal_add m p)). Qed.
Lemma lem1321326 (m : hreal) (n : hreal) (p : hreal) (h1 : n = p) : (hreal_add m n) = (hreal_add m p).
Proof. exact (EQ_MP (@lem1321324 m n p h1) (@lem1321325 m p)). Qed.
Lemma lem1321328 (n : hreal) (m : hreal) (p : hreal) : term11 n m p.
Proof. exact (fun h0 : n = p => @lem1321326 m n p h0). Qed.
Lemma lem1321329 (n : hreal) (m : hreal) (p : hreal) : term12 n m p.
Proof. exact (conj (@lem1321300 m n p) (@lem1321328 n m p)). Qed.
Lemma lem1321330 (m : hreal) (n : hreal) (p : hreal) : (term12 n m p) = (((hreal_add m n) = (hreal_add m p)) = (n = p)).
Proof. exact (@lem32 ((hreal_add m n) = (hreal_add m p)) (n = p)). Qed.
Lemma lem1321331 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1321330 m n p) (@lem1321329 n m p)). Qed.
Lemma lem1321336 (m : hreal) (n : hreal) : term13 m n.
Proof. exact (fun p : hreal => @lem1321331 m n p). Qed.
Lemma lem1321341 (m : hreal) : term14 m.
Proof. exact (fun n : hreal => @lem1321336 m n). Qed.
Lemma lem1321346 : term15.
Proof. exact (fun m : hreal => @lem1321341 m). Qed.

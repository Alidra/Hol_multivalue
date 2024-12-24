Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259488_term_abbrevs.
Require Import thm1248118_spec.
Require Import thm1248132_spec.
Require Import thm1248146_spec.
Require Import thm1248166_spec.
Require Import thm1248167_spec.
Require Import thm1248182_spec.
Require Import thm1248216_spec.
Require Import thm1248292_spec.
Require Import thm1248368_spec.
Require Import thm1248369_spec.
Require Import thm1248384_spec.
Require Import thm1248418_spec.
Require Import thm1248494_spec.
Require Import thm1248822_spec.
Require Import thm1248838_spec.
Require Import thm1248854_spec.
Require Import thm1248870_spec.
Require Import thm1248886_spec.
Require Import thm1248902_spec.
Require Import thm1248918_spec.
Require Import thm1248934_spec.
Require Import thm1259264_spec.
Require Import thm1259269_spec.
Require Import thm1259274_spec.
Require Import thm1259279_spec.
Require Import thm1259284_spec.
Require Import thm1259289_spec.
Require Import thm1259294_spec.
Require Import thm1259299_spec.
Lemma lem1259404 (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (term0 m d q) = (term0 m n d')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248934 d d' d'') (@lem1259264 d'' d q m n d' h1 h2)). Qed.
Lemma lem1259405 (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : (term0 m d q) = (term0 m n d')) : term2 q n d d' d''.
Proof. exact (fun h0 : q = (Nat.add n d'') => @lem1259404 d'' d q m n d' h0 h1). Qed.
Lemma lem1259406 (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (term0 m d q) = (term0 m n d')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248918 d d' d'') (@lem1259269 d'' d q m n d' h1 h2)). Qed.
Lemma lem1259407 (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : (term0 m d q) = (term0 m n d')) : term2 n q d d' d''.
Proof. exact (fun h0 : n = (Nat.add q d'') => @lem1259406 d'' d q m n d' h0 h1). Qed.
Lemma lem1259408 (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : (term0 m d q) = (term0 m n d')) : term3 q n d d' d''.
Proof. exact (conj (@lem1259407 d'' d q m n d' h1) (@lem1259405 d'' d q m n d' h1)). Qed.
Lemma lem1259413 (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : (term0 m d q) = (term0 m n d')) : term4 q n d d'.
Proof. exact (fun d'' : nat => @lem1259408 d'' d q m n d' h1). Qed.
Lemma lem1259414 (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : (term0 m d q) = (term0 m n d')) : term5 d d' n q.
Proof. exact (EQ_MP (@lem1248494 d d' n q) (@lem1259413 d q m n d' h1)). Qed.
Lemma lem1259415 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (Nat.add m n) = (term6 m d q d')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248902 d d' d'') (@lem1259274 d'' n m d q d' h1 h2)). Qed.
Lemma lem1259416 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : (Nat.add m n) = (term6 m d q d')) : term2 q n d d' d''.
Proof. exact (fun h0 : q = (Nat.add n d'') => @lem1259415 d'' n m d q d' h0 h1). Qed.
Lemma lem1259417 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (Nat.add m n) = (term6 m d q d')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248886 d d' d'') (@lem1259279 d'' n m d q d' h1 h2)). Qed.
Lemma lem1259418 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : (Nat.add m n) = (term6 m d q d')) : term2 n q d d' d''.
Proof. exact (fun h0 : n = (Nat.add q d'') => @lem1259417 d'' n m d q d' h0 h1). Qed.
Lemma lem1259419 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : (Nat.add m n) = (term6 m d q d')) : term3 q n d d' d''.
Proof. exact (conj (@lem1259418 d'' n m d q d' h1) (@lem1259416 d'' n m d q d' h1)). Qed.
Lemma lem1259424 (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : (Nat.add m n) = (term6 m d q d')) : term4 q n d d'.
Proof. exact (fun d'' : nat => @lem1259419 d'' n m d q d' h1). Qed.
Lemma lem1259425 (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : (Nat.add m n) = (term6 m d q d')) : term5 d d' n q.
Proof. exact (EQ_MP (@lem1248418 d d' n q) (@lem1259424 n m d q d' h1)). Qed.
Lemma lem1259426 (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : (term0 m d q) = (term0 m n d')) : ((term0 m d q) = (term0 m n d')) = (term5 d d' n q).
Proof. exact (prop_ext (fun h2 : (term0 m d q) = (term0 m n d') => @lem1259414 d q m n d' h1) (fun h2 : term5 d d' n q => @lem1248384 d q m n d' h1)). Qed.
Lemma lem1259428 (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : (term0 m d q) = (term0 m n d')) : term5 d d' n q.
Proof. exact (EQ_MP (@lem1259426 d q m n d' h1) (@lem1248384 d q m n d' h1)). Qed.
Lemma lem1259429 (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : term7 m d d' n q.
Proof. exact (fun h0 : (term0 m d q) = (term0 m n d') => @lem1259428 d q m n d' h0). Qed.
Lemma lem1259430 (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : (Nat.add m n) = (term6 m d q d')) : ((Nat.add m n) = (term6 m d q d')) = (term5 d d' n q).
Proof. exact (prop_ext (fun h2 : (Nat.add m n) = (term6 m d q d') => @lem1259425 n m d q d' h1) (fun h2 : term5 d d' n q => @lem1248369 n m d q d' h1)). Qed.
Lemma lem1259432 (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : (Nat.add m n) = (term6 m d q d')) : term5 d d' n q.
Proof. exact (EQ_MP (@lem1259430 n m d q d' h1) (@lem1248369 n m d q d' h1)). Qed.
Lemma lem1259433 (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : term8 m d d' n q.
Proof. exact (fun h0 : (Nat.add m n) = (term6 m d q d') => @lem1259432 n m d q d' h0). Qed.
Lemma lem1259434 (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : term9 m d d' n q.
Proof. exact (conj (@lem1259433 m d d' n q) (@lem1259429 m d d' n q)). Qed.
Lemma lem1259439 (m : nat) (d : nat) (n : nat) (q : nat) : term10 m d n q.
Proof. exact (fun d' : nat => @lem1259434 m d d' n q). Qed.
Lemma lem1259440 (m : nat) (d : nat) (n : nat) (q : nat) : term11 m d n q.
Proof. exact (EQ_MP (@lem1248368 m d n q) (@lem1259439 m d n q)). Qed.
Lemma lem1259441 (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (Nat.add p q) = (term6 p d n d')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248870 d d' d'') (@lem1259284 d'' q p d n d' h1 h2)). Qed.
Lemma lem1259442 (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p q) = (term6 p d n d')) : term2 q n d d' d''.
Proof. exact (fun h0 : q = (Nat.add n d'') => @lem1259441 d'' q p d n d' h0 h1). Qed.
Lemma lem1259443 (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (Nat.add p q) = (term6 p d n d')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248854 d d' d'') (@lem1259289 d'' q p d n d' h1 h2)). Qed.
Lemma lem1259444 (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p q) = (term6 p d n d')) : term2 n q d d' d''.
Proof. exact (fun h0 : n = (Nat.add q d'') => @lem1259443 d'' q p d n d' h0 h1). Qed.
Lemma lem1259445 (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p q) = (term6 p d n d')) : term3 q n d d' d''.
Proof. exact (conj (@lem1259444 d'' q p d n d' h1) (@lem1259442 d'' q p d n d' h1)). Qed.
Lemma lem1259450 (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p q) = (term6 p d n d')) : term4 q n d d'.
Proof. exact (fun d'' : nat => @lem1259445 d'' q p d n d' h1). Qed.
Lemma lem1259451 (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p q) = (term6 p d n d')) : term5 d d' n q.
Proof. exact (EQ_MP (@lem1248292 d d' n q) (@lem1259450 q p d n d' h1)). Qed.
Lemma lem1259452 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (term0 p d n) = (term0 p q d')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248838 d d' d'') (@lem1259294 d'' d n p q d' h1 h2)). Qed.
Lemma lem1259453 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : (term0 p d n) = (term0 p q d')) : term2 q n d d' d''.
Proof. exact (fun h0 : q = (Nat.add n d'') => @lem1259452 d'' d n p q d' h0 h1). Qed.
Lemma lem1259454 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (term0 p d n) = (term0 p q d')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248822 d d' d'') (@lem1259299 d'' d n p q d' h1 h2)). Qed.
Lemma lem1259455 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : (term0 p d n) = (term0 p q d')) : term2 n q d d' d''.
Proof. exact (fun h0 : n = (Nat.add q d'') => @lem1259454 d'' d n p q d' h0 h1). Qed.
Lemma lem1259456 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : (term0 p d n) = (term0 p q d')) : term3 q n d d' d''.
Proof. exact (conj (@lem1259455 d'' d n p q d' h1) (@lem1259453 d'' d n p q d' h1)). Qed.
Lemma lem1259461 (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : (term0 p d n) = (term0 p q d')) : term4 q n d d'.
Proof. exact (fun d'' : nat => @lem1259456 d'' d n p q d' h1). Qed.
Lemma lem1259462 (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : (term0 p d n) = (term0 p q d')) : term5 d d' n q.
Proof. exact (EQ_MP (@lem1248216 d d' n q) (@lem1259461 d n p q d' h1)). Qed.
Lemma lem1259463 (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p q) = (term6 p d n d')) : ((Nat.add p q) = (term6 p d n d')) = (term5 d d' n q).
Proof. exact (prop_ext (fun h2 : (Nat.add p q) = (term6 p d n d') => @lem1259451 q p d n d' h1) (fun h2 : term5 d d' n q => @lem1248182 q p d n d' h1)). Qed.
Lemma lem1259465 (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p q) = (term6 p d n d')) : term5 d d' n q.
Proof. exact (EQ_MP (@lem1259463 q p d n d' h1) (@lem1248182 q p d n d' h1)). Qed.
Lemma lem1259466 (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : term12 p d d' n q.
Proof. exact (fun h0 : (Nat.add p q) = (term6 p d n d') => @lem1259465 q p d n d' h0). Qed.
Lemma lem1259467 (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : (term0 p d n) = (term0 p q d')) : ((term0 p d n) = (term0 p q d')) = (term5 d d' n q).
Proof. exact (prop_ext (fun h2 : (term0 p d n) = (term0 p q d') => @lem1259462 d n p q d' h1) (fun h2 : term5 d d' n q => @lem1248167 d n p q d' h1)). Qed.
Lemma lem1259469 (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : (term0 p d n) = (term0 p q d')) : term5 d d' n q.
Proof. exact (EQ_MP (@lem1259467 d n p q d' h1) (@lem1248167 d n p q d' h1)). Qed.
Lemma lem1259470 (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : term13 p d d' n q.
Proof. exact (fun h0 : (term0 p d n) = (term0 p q d') => @lem1259469 d n p q d' h0). Qed.
Lemma lem1259471 (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) : term14 p d d' n q.
Proof. exact (conj (@lem1259470 p d d' n q) (@lem1259466 p d d' n q)). Qed.
Lemma lem1259476 (p : nat) (d : nat) (n : nat) (q : nat) : term15 p d n q.
Proof. exact (fun d' : nat => @lem1259471 p d d' n q). Qed.
Lemma lem1259477 (d : nat) (p : nat) (n : nat) (q : nat) : term16 d p n q.
Proof. exact (EQ_MP (@lem1248166 d p n q) (@lem1259476 p d n q)). Qed.
Lemma lem1259478 (n : nat) (q : nat) (p : nat) (m : nat) (d : nat) (h1 : p = (Nat.add m d)) : term17 d m p n q.
Proof. exact (EQ_MP (@lem1248146 n q p m d h1) (@lem1259440 m d n q)). Qed.
Lemma lem1259479 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : term18 d m p n q.
Proof. exact (fun h0 : p = (Nat.add m d) => @lem1259478 n q p m d h0). Qed.
Lemma lem1259480 (n : nat) (q : nat) (m : nat) (p : nat) (d : nat) (h1 : m = (Nat.add p d)) : term17 d m p n q.
Proof. exact (EQ_MP (@lem1248132 n q m p d h1) (@lem1259477 d p n q)). Qed.
Lemma lem1259481 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : term19 d m p n q.
Proof. exact (fun h0 : m = (Nat.add p d) => @lem1259480 n q m p d h0). Qed.
Lemma lem1259482 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : term20 d m p n q.
Proof. exact (conj (@lem1259481 d m p n q) (@lem1259479 d m p n q)). Qed.
Lemma lem1259487 (m : nat) (p : nat) (n : nat) (q : nat) : term21 m p n q.
Proof. exact (fun d : nat => @lem1259482 d m p n q). Qed.
Lemma lem1259488 (m : nat) (p : nat) (n : nat) (q : nat) : term22 m p n q.
Proof. exact (EQ_MP (@lem1248118 m p n q) (@lem1259487 m p n q)). Qed.

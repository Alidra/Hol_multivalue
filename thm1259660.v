Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259660_term_abbrevs.
Require Import thm1247241_spec.
Require Import thm1247255_spec.
Require Import thm1247269_spec.
Require Import thm1247289_spec.
Require Import thm1247290_spec.
Require Import thm1247318_spec.
Require Import thm1247338_spec.
Require Import thm1247414_spec.
Require Import thm1247415_spec.
Require Import thm1247430_spec.
Require Import thm1247464_spec.
Require Import thm1247478_spec.
Require Import thm1247492_spec.
Require Import thm1247512_spec.
Require Import thm1247513_spec.
Require Import thm1247528_spec.
Require Import thm1247562_spec.
Require Import thm1247563_spec.
Require Import thm1247578_spec.
Require Import thm1248566_spec.
Require Import thm1248582_spec.
Require Import thm1259374_spec.
Require Import thm1259379_spec.
Require Import thm1259396_spec.
Require Import thm1259397_spec.
Require Import thm1259398_spec.
Require Import thm1259399_spec.
Require Import thm1259400_spec.
Require Import thm1259401_spec.
Lemma lem1259570 (d : nat) (m : nat) (d' : nat) (d'' : nat) (h1 : (Nat.add m d) = (term0 m d' d'')) : ((Nat.add m d) = (term0 m d' d'')) = (term1 d d' d'').
Proof. exact (prop_ext (fun h2 : (Nat.add m d) = (term0 m d' d'') => @lem1259396 d m d' d'' h1) (fun h2 : term1 d d' d'' => @lem1247578 d m d' d'' h1)). Qed.
Lemma lem1259572 (d : nat) (m : nat) (d' : nat) (d'' : nat) (h1 : (Nat.add m d) = (term0 m d' d'')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1259570 d m d' d'' h1) (@lem1247578 d m d' d'' h1)). Qed.
Lemma lem1259573 (m : nat) (d : nat) (d' : nat) (d'' : nat) : term2 m d d' d''.
Proof. exact (fun h0 : (Nat.add m d) = (term0 m d' d'') => @lem1259572 d m d' d'' h0). Qed.
Lemma lem1259574 (d' : nat) (m : nat) (d : nat) (d'' : nat) (h1 : (Nat.add m d') = (term0 m d d'')) : ((Nat.add m d') = (term0 m d d'')) = (term1 d d' d'').
Proof. exact (prop_ext (fun h2 : (Nat.add m d') = (term0 m d d'') => @lem1259397 d' m d d'' h1) (fun h2 : term1 d d' d'' => @lem1247563 d' m d d'' h1)). Qed.
Lemma lem1259576 (d' : nat) (m : nat) (d : nat) (d'' : nat) (h1 : (Nat.add m d') = (term0 m d d'')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1259574 d' m d d'' h1) (@lem1247563 d' m d d'' h1)). Qed.
Lemma lem1259577 (m : nat) (d : nat) (d' : nat) (d'' : nat) : term3 m d d' d''.
Proof. exact (fun h0 : (Nat.add m d') = (term0 m d d'') => @lem1259576 d' m d d'' h0). Qed.
Lemma lem1259578 (m : nat) (d : nat) (d' : nat) (d'' : nat) : term4 m d d' d''.
Proof. exact (conj (@lem1259577 m d d' d'') (@lem1259573 m d d' d'')). Qed.
Lemma lem1259583 (m : nat) (d : nat) (d' : nat) : term5 m d d'.
Proof. exact (fun d'' : nat => @lem1259578 m d d' d''). Qed.
Lemma lem1259584 (d' : nat) (m : nat) (d : nat) : term6 d' m d.
Proof. exact (EQ_MP (@lem1247562 d' m d) (@lem1259583 m d d')). Qed.
Lemma lem1259585 (d' : nat) (d : nat) (n : nat) (d'' : nat) (h1 : (term0 n d' d) = (Nat.add n d'')) : ((term0 n d' d) = (Nat.add n d'')) = (term1 d d' d'').
Proof. exact (prop_ext (fun h2 : (term0 n d' d) = (Nat.add n d'') => @lem1259398 d' d n d'' h1) (fun h2 : term1 d d' d'' => @lem1247528 d' d n d'' h1)). Qed.
Lemma lem1259587 (d' : nat) (d : nat) (n : nat) (d'' : nat) (h1 : (term0 n d' d) = (Nat.add n d'')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1259585 d' d n d'' h1) (@lem1247528 d' d n d'' h1)). Qed.
Lemma lem1259588 (n : nat) (d : nat) (d' : nat) (d'' : nat) : term7 n d d' d''.
Proof. exact (fun h0 : (term0 n d' d) = (Nat.add n d'') => @lem1259587 d' d n d'' h0). Qed.
Lemma lem1259589 (n : nat) (d' : nat) (d : nat) (d'' : nat) (h1 : n = (term8 n d' d d'')) : (n = (term8 n d' d d'')) = (term1 d d' d'').
Proof. exact (prop_ext (fun h2 : n = (term8 n d' d d'') => @lem1259399 n d' d d'' h1) (fun h2 : term1 d d' d'' => @lem1247513 n d' d d'' h1)). Qed.
Lemma lem1259591 (n : nat) (d' : nat) (d : nat) (d'' : nat) (h1 : n = (term8 n d' d d'')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1259589 n d' d d'' h1) (@lem1247513 n d' d d'' h1)). Qed.
Lemma lem1259592 (n : nat) (d : nat) (d' : nat) (d'' : nat) : term9 n d d' d''.
Proof. exact (fun h0 : n = (term8 n d' d d'') => @lem1259591 n d' d d'' h0). Qed.
Lemma lem1259593 (n : nat) (d : nat) (d' : nat) (d'' : nat) : term10 n d d' d''.
Proof. exact (conj (@lem1259592 n d d' d'') (@lem1259588 n d d' d'')). Qed.
Lemma lem1259598 (n : nat) (d : nat) (d' : nat) : term11 n d d'.
Proof. exact (fun d'' : nat => @lem1259593 n d d' d''). Qed.
Lemma lem1259599 (n : nat) (d' : nat) (d : nat) : term12 n d' d.
Proof. exact (EQ_MP (@lem1247512 n d' d) (@lem1259598 n d d')). Qed.
Lemma lem1259600 (d : nat) (n : nat) (m : nat) (d' : nat) (h1 : n = (Nat.add m d')) : term13 d' n m d.
Proof. exact (EQ_MP (@lem1247492 d n m d' h1) (@lem1259584 d' m d)). Qed.
Lemma lem1259601 (d' : nat) (n : nat) (m : nat) (d : nat) : term14 d' n m d.
Proof. exact (fun h0 : n = (Nat.add m d') => @lem1259600 d n m d' h0). Qed.
Lemma lem1259602 (d : nat) (m : nat) (n : nat) (d' : nat) (h1 : m = (Nat.add n d')) : term13 d' n m d.
Proof. exact (EQ_MP (@lem1247478 d m n d' h1) (@lem1259599 n d' d)). Qed.
Lemma lem1259603 (d' : nat) (n : nat) (m : nat) (d : nat) : term15 d' n m d.
Proof. exact (fun h0 : m = (Nat.add n d') => @lem1259602 d m n d' h0). Qed.
Lemma lem1259604 (d' : nat) (n : nat) (m : nat) (d : nat) : term16 d' n m d.
Proof. exact (conj (@lem1259603 d' n m d) (@lem1259601 d' n m d)). Qed.
Lemma lem1259609 (n : nat) (m : nat) (d : nat) : term17 n m d.
Proof. exact (fun d' : nat => @lem1259604 d' n m d). Qed.
Lemma lem1259610 (n : nat) (m : nat) (d : nat) : term18 n m d.
Proof. exact (EQ_MP (@lem1247464 n m d) (@lem1259609 n m d)). Qed.
Lemma lem1259611 (p : nat) (d : nat) (d' : nat) (d'' : nat) (h1 : p = (term8 p d d' d'')) : (p = (term8 p d d' d'')) = (term1 d d' d'').
Proof. exact (prop_ext (fun h2 : p = (term8 p d d' d'') => @lem1259400 p d d' d'' h1) (fun h2 : term1 d d' d'' => @lem1247430 p d d' d'' h1)). Qed.
Lemma lem1259613 (p : nat) (d : nat) (d' : nat) (d'' : nat) (h1 : p = (term8 p d d' d'')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1259611 p d d' d'' h1) (@lem1247430 p d d' d'' h1)). Qed.
Lemma lem1259614 (p : nat) (d : nat) (d' : nat) (d'' : nat) : term19 p d d' d''.
Proof. exact (fun h0 : p = (term8 p d d' d'') => @lem1259613 p d d' d'' h0). Qed.
Lemma lem1259615 (d : nat) (d' : nat) (p : nat) (d'' : nat) (h1 : (term0 p d d') = (Nat.add p d'')) : ((term0 p d d') = (Nat.add p d'')) = (term1 d d' d'').
Proof. exact (prop_ext (fun h2 : (term0 p d d') = (Nat.add p d'') => @lem1259401 d d' p d'' h1) (fun h2 : term1 d d' d'' => @lem1247415 d d' p d'' h1)). Qed.
Lemma lem1259617 (d : nat) (d' : nat) (p : nat) (d'' : nat) (h1 : (term0 p d d') = (Nat.add p d'')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1259615 d d' p d'' h1) (@lem1247415 d d' p d'' h1)). Qed.
Lemma lem1259618 (p : nat) (d : nat) (d' : nat) (d'' : nat) : term20 p d d' d''.
Proof. exact (fun h0 : (term0 p d d') = (Nat.add p d'') => @lem1259617 d d' p d'' h0). Qed.
Lemma lem1259619 (p : nat) (d : nat) (d' : nat) (d'' : nat) : term21 p d d' d''.
Proof. exact (conj (@lem1259618 p d d' d'') (@lem1259614 p d d' d'')). Qed.
Lemma lem1259624 (p : nat) (d : nat) (d' : nat) : term22 p d d'.
Proof. exact (fun d'' : nat => @lem1259619 p d d' d''). Qed.
Lemma lem1259625 (d : nat) (d' : nat) (p : nat) : term23 d d' p.
Proof. exact (EQ_MP (@lem1247414 d d' p) (@lem1259624 p d d')). Qed.
Lemma lem1259626 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : p = (Nat.add n d'')) (h2 : (Nat.add p d) = (Nat.add n d')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248582 d d' d'') (@lem1259374 d'' p d n d' h1 h2)). Qed.
Lemma lem1259627 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p d) = (Nat.add n d')) : term24 p n d d' d''.
Proof. exact (fun h0 : p = (Nat.add n d'') => @lem1259626 d'' p d n d' h0 h1). Qed.
Lemma lem1259628 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : n = (Nat.add p d'')) (h2 : (Nat.add p d) = (Nat.add n d')) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248566 d d' d'') (@lem1259379 d'' p d n d' h1 h2)). Qed.
Lemma lem1259629 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p d) = (Nat.add n d')) : term24 n p d d' d''.
Proof. exact (fun h0 : n = (Nat.add p d'') => @lem1259628 d'' p d n d' h0 h1). Qed.
Lemma lem1259630 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p d) = (Nat.add n d')) : term25 p n d d' d''.
Proof. exact (conj (@lem1259629 d'' p d n d' h1) (@lem1259627 d'' p d n d' h1)). Qed.
Lemma lem1259635 (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p d) = (Nat.add n d')) : term26 p n d d'.
Proof. exact (fun d'' : nat => @lem1259630 d'' p d n d' h1). Qed.
Lemma lem1259636 (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p d) = (Nat.add n d')) : term27 d d' n p.
Proof. exact (EQ_MP (@lem1247338 d d' n p) (@lem1259635 p d n d' h1)). Qed.
Lemma lem1259637 (n : nat) (p : nat) (d : nat) (d' : nat) (h1 : n = (term0 p d d')) : term27 d d' n p.
Proof. exact (EQ_MP (@lem1247318 n p d d' h1) (@lem1259625 d d' p)). Qed.
Lemma lem1259638 (d : nat) (d' : nat) (n : nat) (p : nat) : term28 d d' n p.
Proof. exact (fun h0 : n = (term0 p d d') => @lem1259637 n p d d' h0). Qed.
Lemma lem1259639 (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p d) = (Nat.add n d')) : ((Nat.add p d) = (Nat.add n d')) = (term27 d d' n p).
Proof. exact (prop_ext (fun h2 : (Nat.add p d) = (Nat.add n d') => @lem1259636 p d n d' h1) (fun h2 : term27 d d' n p => @lem1247290 p d n d' h1)). Qed.
Lemma lem1259641 (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : (Nat.add p d) = (Nat.add n d')) : term27 d d' n p.
Proof. exact (EQ_MP (@lem1259639 p d n d' h1) (@lem1247290 p d n d' h1)). Qed.
Lemma lem1259642 (d : nat) (d' : nat) (n : nat) (p : nat) : term29 d d' n p.
Proof. exact (fun h0 : (Nat.add p d) = (Nat.add n d') => @lem1259641 p d n d' h0). Qed.
Lemma lem1259643 (d : nat) (d' : nat) (n : nat) (p : nat) : term30 d d' n p.
Proof. exact (conj (@lem1259642 d d' n p) (@lem1259638 d d' n p)). Qed.
Lemma lem1259648 (d : nat) (n : nat) (p : nat) : term31 d n p.
Proof. exact (fun d' : nat => @lem1259643 d d' n p). Qed.
Lemma lem1259649 (d : nat) (n : nat) (p : nat) : term32 d n p.
Proof. exact (EQ_MP (@lem1247289 d n p) (@lem1259648 d n p)). Qed.
Lemma lem1259650 (n : nat) (p : nat) (m : nat) (d : nat) (h1 : p = (Nat.add m d)) : term33 d m n p.
Proof. exact (EQ_MP (@lem1247269 n p m d h1) (@lem1259610 n m d)). Qed.
Lemma lem1259651 (d : nat) (m : nat) (n : nat) (p : nat) : term34 d m n p.
Proof. exact (fun h0 : p = (Nat.add m d) => @lem1259650 n p m d h0). Qed.
Lemma lem1259652 (n : nat) (m : nat) (p : nat) (d : nat) (h1 : m = (Nat.add p d)) : term33 d m n p.
Proof. exact (EQ_MP (@lem1247255 n m p d h1) (@lem1259649 d n p)). Qed.
Lemma lem1259653 (d : nat) (m : nat) (n : nat) (p : nat) : term35 d m n p.
Proof. exact (fun h0 : m = (Nat.add p d) => @lem1259652 n m p d h0). Qed.
Lemma lem1259654 (d : nat) (m : nat) (n : nat) (p : nat) : term36 d m n p.
Proof. exact (conj (@lem1259653 d m n p) (@lem1259651 d m n p)). Qed.
Lemma lem1259659 (m : nat) (n : nat) (p : nat) : term37 m n p.
Proof. exact (fun d : nat => @lem1259654 d m n p). Qed.
Lemma lem1259660 (m : nat) (n : nat) (p : nat) : term38 m n p.
Proof. exact (EQ_MP (@lem1247241 m n p) (@lem1259659 m n p)). Qed.

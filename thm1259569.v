Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259569_term_abbrevs.
Require Import thm1247612_spec.
Require Import thm1247613_spec.
Require Import thm1247628_spec.
Require Import thm1247662_spec.
Require Import thm1247738_spec.
Require Import thm1247814_spec.
Require Import thm1247890_spec.
Require Import thm1247966_spec.
Require Import thm1248042_spec.
Require Import thm1248694_spec.
Require Import thm1248710_spec.
Require Import thm1248726_spec.
Require Import thm1248742_spec.
Require Import thm1248758_spec.
Require Import thm1248774_spec.
Require Import thm1248790_spec.
Require Import thm1248806_spec.
Require Import thm1259304_spec.
Require Import thm1259309_spec.
Require Import thm1259314_spec.
Require Import thm1259319_spec.
Require Import thm1259324_spec.
Require Import thm1259329_spec.
Require Import thm1259334_spec.
Require Import thm1259339_spec.
Lemma lem1259489 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add p q) = (term0 m n d)) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248806 d d' d'') (@lem1259304 d' d'' p q m n d h1 h2 h3)). Qed.
Lemma lem1259490 (d'' : nat) (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add p q) = (term0 m n d)) : term2 q n d d' d''.
Proof. exact (fun h0 : q = (Nat.add n d'') => @lem1259489 d' d'' p q m n d h1 h0 h2). Qed.
Lemma lem1259491 (d'' : nat) (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : n = (Nat.add q d'')) (h2 : p = (Nat.add m d')) (h3 : (Nat.add p q) = (term0 m n d)) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248790 d d' d'') (@lem1259309 d'' d' p q m n d h1 h2 h3)). Qed.
Lemma lem1259492 (d'' : nat) (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add p q) = (term0 m n d)) : term2 n q d d' d''.
Proof. exact (fun h0 : n = (Nat.add q d'') => @lem1259491 d'' d' p q m n d h0 h1 h2). Qed.
Lemma lem1259493 (d'' : nat) (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add p q) = (term0 m n d)) : term3 q n d d' d''.
Proof. exact (conj (@lem1259492 d'' d' p q m n d h1 h2) (@lem1259490 d'' d' p q m n d h1 h2)). Qed.
Lemma lem1259498 (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add p q) = (term0 m n d)) : term4 q n d d'.
Proof. exact (fun d'' : nat => @lem1259493 d'' d' p q m n d h1 h2). Qed.
Lemma lem1259500 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add p q) = (term0 m n d)) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248774 d d' d'') (@lem1259314 d' d'' p q m n d h1 h2 h3)). Qed.
Lemma lem1259501 (d'' : nat) (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : (Nat.add p q) = (term0 m n d)) : term2 q n d d' d''.
Proof. exact (fun h0 : q = (Nat.add n d'') => @lem1259500 d' d'' p q m n d h1 h0 h2). Qed.
Lemma lem1259502 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add p q) = (term0 m n d)) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248758 d d' d'') (@lem1259319 d' d'' p q m n d h1 h2 h3)). Qed.
Lemma lem1259503 (d'' : nat) (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : (Nat.add p q) = (term0 m n d)) : term2 n q d d' d''.
Proof. exact (fun h0 : n = (Nat.add q d'') => @lem1259502 d' d'' p q m n d h1 h0 h2). Qed.
Lemma lem1259504 (d'' : nat) (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : (Nat.add p q) = (term0 m n d)) : term3 q n d d' d''.
Proof. exact (conj (@lem1259503 d'' d' p q m n d h1 h2) (@lem1259501 d'' d' p q m n d h1 h2)). Qed.
Lemma lem1259509 (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : (Nat.add p q) = (term0 m n d)) : term4 q n d d'.
Proof. exact (fun d'' : nat => @lem1259504 d'' d' p q m n d h1 h2). Qed.
Lemma lem1259511 (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add p q) = (term0 m n d)) : term5 d d' n q.
Proof. exact (EQ_MP (@lem1248042 d d' n q) (@lem1259498 d' p q m n d h1 h2)). Qed.
Lemma lem1259512 (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : (Nat.add p q) = (term0 m n d)) : term6 p m d d' n q.
Proof. exact (fun h0 : p = (Nat.add m d') => @lem1259511 d' p q m n d h0 h1). Qed.
Lemma lem1259513 (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : (Nat.add p q) = (term0 m n d)) : term5 d d' n q.
Proof. exact (EQ_MP (@lem1247966 d d' n q) (@lem1259509 d' p q m n d h1 h2)). Qed.
Lemma lem1259514 (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : (Nat.add p q) = (term0 m n d)) : term6 m p d d' n q.
Proof. exact (fun h0 : m = (Nat.add p d') => @lem1259513 d' p q m n d h0 h1). Qed.
Lemma lem1259515 (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : (Nat.add p q) = (term0 m n d)) : term7 p m d d' n q.
Proof. exact (conj (@lem1259514 d' p q m n d h1) (@lem1259512 d' p q m n d h1)). Qed.
Lemma lem1259520 (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : (Nat.add p q) = (term0 m n d)) : term8 p m d n q.
Proof. exact (fun d' : nat => @lem1259515 d' p q m n d h1). Qed.
Lemma lem1259521 (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : (Nat.add p q) = (term0 m n d)) : term9 d m p n q.
Proof. exact (EQ_MP (@lem1247890 d m p n q) (@lem1259520 p q m n d h1)). Qed.
Lemma lem1259522 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add m n) = (term0 p q d)) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248742 d d' d'') (@lem1259324 d' d'' m n p q d h1 h2 h3)). Qed.
Lemma lem1259523 (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add m n) = (term0 p q d)) : term2 q n d d' d''.
Proof. exact (fun h0 : q = (Nat.add n d'') => @lem1259522 d' d'' m n p q d h1 h0 h2). Qed.
Lemma lem1259524 (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : n = (Nat.add q d'')) (h2 : p = (Nat.add m d')) (h3 : (Nat.add m n) = (term0 p q d)) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248726 d d' d'') (@lem1259329 d'' d' m n p q d h1 h2 h3)). Qed.
Lemma lem1259525 (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add m n) = (term0 p q d)) : term2 n q d d' d''.
Proof. exact (fun h0 : n = (Nat.add q d'') => @lem1259524 d'' d' m n p q d h0 h1 h2). Qed.
Lemma lem1259526 (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add m n) = (term0 p q d)) : term3 q n d d' d''.
Proof. exact (conj (@lem1259525 d'' d' m n p q d h1 h2) (@lem1259523 d'' d' m n p q d h1 h2)). Qed.
Lemma lem1259531 (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add m n) = (term0 p q d)) : term4 q n d d'.
Proof. exact (fun d'' : nat => @lem1259526 d'' d' m n p q d h1 h2). Qed.
Lemma lem1259533 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add m n) = (term0 p q d)) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248710 d d' d'') (@lem1259334 d' d'' m n p q d h1 h2 h3)). Qed.
Lemma lem1259534 (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : (Nat.add m n) = (term0 p q d)) : term2 q n d d' d''.
Proof. exact (fun h0 : q = (Nat.add n d'') => @lem1259533 d' d'' m n p q d h1 h0 h2). Qed.
Lemma lem1259535 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add m n) = (term0 p q d)) : term1 d d' d''.
Proof. exact (EQ_MP (@lem1248694 d d' d'') (@lem1259339 d' d'' m n p q d h1 h2 h3)). Qed.
Lemma lem1259536 (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : (Nat.add m n) = (term0 p q d)) : term2 n q d d' d''.
Proof. exact (fun h0 : n = (Nat.add q d'') => @lem1259535 d' d'' m n p q d h1 h0 h2). Qed.
Lemma lem1259537 (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : (Nat.add m n) = (term0 p q d)) : term3 q n d d' d''.
Proof. exact (conj (@lem1259536 d'' d' m n p q d h1 h2) (@lem1259534 d'' d' m n p q d h1 h2)). Qed.
Lemma lem1259542 (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : (Nat.add m n) = (term0 p q d)) : term4 q n d d'.
Proof. exact (fun d'' : nat => @lem1259537 d'' d' m n p q d h1 h2). Qed.
Lemma lem1259544 (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add m n) = (term0 p q d)) : term5 d d' n q.
Proof. exact (EQ_MP (@lem1247814 d d' n q) (@lem1259531 d' m n p q d h1 h2)). Qed.
Lemma lem1259545 (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : (Nat.add m n) = (term0 p q d)) : term6 p m d d' n q.
Proof. exact (fun h0 : p = (Nat.add m d') => @lem1259544 d' m n p q d h0 h1). Qed.
Lemma lem1259546 (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : (Nat.add m n) = (term0 p q d)) : term5 d d' n q.
Proof. exact (EQ_MP (@lem1247738 d d' n q) (@lem1259542 d' m n p q d h1 h2)). Qed.
Lemma lem1259547 (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : (Nat.add m n) = (term0 p q d)) : term6 m p d d' n q.
Proof. exact (fun h0 : m = (Nat.add p d') => @lem1259546 d' m n p q d h0 h1). Qed.
Lemma lem1259548 (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : (Nat.add m n) = (term0 p q d)) : term7 p m d d' n q.
Proof. exact (conj (@lem1259547 d' m n p q d h1) (@lem1259545 d' m n p q d h1)). Qed.
Lemma lem1259553 (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : (Nat.add m n) = (term0 p q d)) : term8 p m d n q.
Proof. exact (fun d' : nat => @lem1259548 d' m n p q d h1). Qed.
Lemma lem1259554 (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : (Nat.add m n) = (term0 p q d)) : term9 d m p n q.
Proof. exact (EQ_MP (@lem1247662 d m p n q) (@lem1259553 m n p q d h1)). Qed.
Lemma lem1259555 (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : (Nat.add p q) = (term0 m n d)) : ((Nat.add p q) = (term0 m n d)) = (term9 d m p n q).
Proof. exact (prop_ext (fun h2 : (Nat.add p q) = (term0 m n d) => @lem1259521 p q m n d h1) (fun h2 : term9 d m p n q => @lem1247628 p q m n d h1)). Qed.
Lemma lem1259557 (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : (Nat.add p q) = (term0 m n d)) : term9 d m p n q.
Proof. exact (EQ_MP (@lem1259555 p q m n d h1) (@lem1247628 p q m n d h1)). Qed.
Lemma lem1259558 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : term10 d m p n q.
Proof. exact (fun h0 : (Nat.add p q) = (term0 m n d) => @lem1259557 p q m n d h0). Qed.
Lemma lem1259559 (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : (Nat.add m n) = (term0 p q d)) : ((Nat.add m n) = (term0 p q d)) = (term9 d m p n q).
Proof. exact (prop_ext (fun h2 : (Nat.add m n) = (term0 p q d) => @lem1259554 m n p q d h1) (fun h2 : term9 d m p n q => @lem1247613 m n p q d h1)). Qed.
Lemma lem1259561 (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : (Nat.add m n) = (term0 p q d)) : term9 d m p n q.
Proof. exact (EQ_MP (@lem1259559 m n p q d h1) (@lem1247613 m n p q d h1)). Qed.
Lemma lem1259562 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : term11 d m p n q.
Proof. exact (fun h0 : (Nat.add m n) = (term0 p q d) => @lem1259561 m n p q d h0). Qed.
Lemma lem1259563 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : term12 d m p n q.
Proof. exact (conj (@lem1259562 d m p n q) (@lem1259558 d m p n q)). Qed.
Lemma lem1259568 (m : nat) (p : nat) (n : nat) (q : nat) : term13 m p n q.
Proof. exact (fun d : nat => @lem1259563 d m p n q). Qed.
Lemma lem1259569 (m : nat) (p : nat) (n : nat) (q : nat) : term14 m p n q.
Proof. exact (EQ_MP (@lem1247612 m p n q) (@lem1259568 m p n q)). Qed.

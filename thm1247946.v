Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247946_term_abbrevs.
Require Import thm1247628_spec.
Lemma lem1247919 (p : nat) (m : nat) (d' : nat) (h1 : p = (Nat.add m d')) : p = (Nat.add m d').
Proof. exact (h1). Qed.
Lemma lem1247934 (q : nat) (m : nat) (n : nat) (d : nat) : (term0 q m n d) = (term0 q m n d).
Proof. exact (eq_refl (term0 q m n d)). Qed.
Lemma lem1247935 (q : nat) (n : nat) (d : nat) (p : nat) (m : nat) (d' : nat) (h1 : p = (Nat.add m d')) : (term1 q m n d p) = (term2 q n d m d').
Proof. exact (MK_COMB (@lem1247934 q m n d) (@lem1247919 p m d' h1)). Qed.
Lemma lem1247936 (d' : nat) (q : nat) (m : nat) (n : nat) (d : nat) : (term2 q n d m d') = ((term3 m d' q) = (term3 m n d)).
Proof. exact (eq_refl (term2 q n d m d')). Qed.
Lemma lem1247937 (q : nat) (m : nat) (n : nat) (d : nat) (p : nat) : (term4 q m n d p) = (term4 q m n d p).
Proof. exact (eq_refl (term4 q m n d p)). Qed.
Lemma lem1247938 (p : nat) (d' : nat) (q : nat) (m : nat) (n : nat) (d : nat) : ((term1 q m n d p) = (term2 q n d m d')) = ((term1 q m n d p) = ((term3 m d' q) = (term3 m n d))).
Proof. exact (MK_COMB (@lem1247937 q m n d p) (@lem1247936 d' q m n d)). Qed.
Lemma lem1247939 (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) : (term1 q m n d p) = ((Nat.add p q) = (term3 m n d)).
Proof. exact (eq_refl (term1 q m n d p)). Qed.
Lemma lem1247940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247941 (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) : (term4 q m n d p) = (term5 p q m n d).
Proof. exact (MK_COMB (@lem1247940) (@lem1247939 p q m n d)). Qed.
Lemma lem1247942 (d' : nat) (q : nat) (m : nat) (n : nat) (d : nat) : ((term3 m d' q) = (term3 m n d)) = ((term3 m d' q) = (term3 m n d)).
Proof. exact (eq_refl ((term3 m d' q) = (term3 m n d))). Qed.
Lemma lem1247943 (p : nat) (d' : nat) (q : nat) (m : nat) (n : nat) (d : nat) : ((term1 q m n d p) = ((term3 m d' q) = (term3 m n d))) = (((Nat.add p q) = (term3 m n d)) = ((term3 m d' q) = (term3 m n d))).
Proof. exact (MK_COMB (@lem1247941 p q m n d) (@lem1247942 d' q m n d)). Qed.
Lemma lem1247944 (p : nat) (d' : nat) (q : nat) (m : nat) (n : nat) (d : nat) : ((term1 q m n d p) = (term2 q n d m d')) = (((Nat.add p q) = (term3 m n d)) = ((term3 m d' q) = (term3 m n d))).
Proof. exact (TRANS (@lem1247938 p d' q m n d) (@lem1247943 p d' q m n d)). Qed.
Lemma lem1247945 (q : nat) (n : nat) (d : nat) (p : nat) (m : nat) (d' : nat) (h1 : p = (Nat.add m d')) : ((Nat.add p q) = (term3 m n d)) = ((term3 m d' q) = (term3 m n d)).
Proof. exact (EQ_MP (@lem1247944 p d' q m n d) (@lem1247935 q n d p m d' h1)). Qed.
Lemma lem1247946 (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add p q) = (term3 m n d)) : (term3 m d' q) = (term3 m n d).
Proof. exact (EQ_MP (@lem1247945 q n d p m d' h1) (@lem1247628 p q m n d h2)). Qed.

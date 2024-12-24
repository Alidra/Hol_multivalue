Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_DIST_term_abbrevs.
Require Import DIST_LADD_0_spec.
Require Import DIST_SYM_spec.
Require Import LE_CASES_spec.
Require Import LE_EXISTS_spec.
Require Import NADD_DIST_LEMMA_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem1266958 (m : nat) : term0 m.
Proof. exact (@lem1244997 m). Qed.
Lemma lem1266959 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1266960 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1266959 m) (@lem1266958 m)). Qed.
Lemma lem1266961 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1266960 m n). Qed.
Lemma lem1266962 (n : nat) (m : nat) : (term2 m n) = ((term3 m n) = (term3 n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1266964 (m : nat) : term4 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem1266965 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1266966 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1266965 m) (@lem1266964 m)). Qed.
Lemma lem1266967 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1266966 m n). Qed.
Lemma lem1266968 (n : nat) (m : nat) : (term6 m n) = ((Peano.le m n) = (term7 n m)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1266970 (m : nat) : term8 m.
Proof. exact (@lem96155 m). Qed.
Lemma lem1266971 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem1266972 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1266971 m) (@lem1266970 m)). Qed.
Lemma lem1266973 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem1266972 m n). Qed.
Lemma lem1266974 (n : nat) (m : nat) : (term10 m n) = (term11 n m).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem1266975 (n : nat) (m : nat) : term11 n m.
Proof. exact (EQ_MP (@lem1266974 n m) (@lem1266973 m n)). Qed.
Lemma lem1266976 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1266977 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem1266978 (x : nadd) : term12 x.
Proof. exact (@lem1266957 x). Qed.
Lemma lem1266979 (x : nadd) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1266980 (x : nadd) : term13 x.
Proof. exact (EQ_MP (@lem1266979 x) (@lem1266978 x)). Qed.
Lemma lem1266981 (x : nadd) (B : nat) (h1 : term14 x B) : term14 x B.
Proof. exact (h1). Qed.
Lemma lem1266982 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1266984 (n : nat) (m : nat) : (Peano.le m n) = (term7 n m).
Proof. exact (EQ_MP (@lem1266968 n m) (@lem1266967 m n)). Qed.
Lemma lem1266985 (m : nat) (n : nat) (h1 : Peano.le m n) : term7 n m.
Proof. exact (EQ_MP (@lem1266984 n m) (@lem1266982 m n h1)). Qed.
Lemma lem1266986 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem1266987 (x : nadd) (B : nat) (m : nat) : (term15 x B m) = (term15 x B m).
Proof. exact (eq_refl (term15 x B m)). Qed.
Lemma lem1266988 (x : nadd) (B : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term16 x B m n) = (term17 x B m d).
Proof. exact (MK_COMB (@lem1266987 x B m) (@lem1266986 n m d h1)). Qed.
Lemma lem1266989 (x : nadd) (B : nat) (m : nat) (d : nat) : (term17 x B m d) = (term18 x B m d).
Proof. exact (eq_refl (term17 x B m d)). Qed.
Lemma lem1266990 (x : nadd) (B : nat) (m : nat) (n : nat) : (term19 x B m n) = (term19 x B m n).
Proof. exact (eq_refl (term19 x B m n)). Qed.
Lemma lem1266991 (n : nat) (x : nadd) (B : nat) (m : nat) (d : nat) : ((term16 x B m n) = (term17 x B m d)) = ((term16 x B m n) = (term18 x B m d)).
Proof. exact (MK_COMB (@lem1266990 x B m n) (@lem1266989 x B m d)). Qed.
Lemma lem1266992 (x : nadd) (B : nat) (m : nat) (n : nat) : (term16 x B m n) = (term20 x B m n).
Proof. exact (eq_refl (term16 x B m n)). Qed.
Lemma lem1266993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1266994 (x : nadd) (B : nat) (m : nat) (n : nat) : (term19 x B m n) = (term21 x B m n).
Proof. exact (MK_COMB (@lem1266993) (@lem1266992 x B m n)). Qed.
Lemma lem1266995 (x : nadd) (B : nat) (m : nat) (d : nat) : (term18 x B m d) = (term18 x B m d).
Proof. exact (eq_refl (term18 x B m d)). Qed.
Lemma lem1266996 (n : nat) (x : nadd) (B : nat) (m : nat) (d : nat) : ((term16 x B m n) = (term18 x B m d)) = ((term20 x B m n) = (term18 x B m d)).
Proof. exact (MK_COMB (@lem1266994 x B m n) (@lem1266995 x B m d)). Qed.
Lemma lem1266997 (n : nat) (x : nadd) (B : nat) (m : nat) (d : nat) : ((term16 x B m n) = (term17 x B m d)) = ((term20 x B m n) = (term18 x B m d)).
Proof. exact (TRANS (@lem1266991 n x B m d) (@lem1266996 n x B m d)). Qed.
Lemma lem1266998 (x : nadd) (B : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term20 x B m n) = (term18 x B m d).
Proof. exact (EQ_MP (@lem1266997 n x B m d) (@lem1266988 x B n m d h1)). Qed.
Lemma lem1266999 (x : nadd) (B : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term18 x B m d) = (term20 x B m n).
Proof. exact (SYM (@lem1266998 x B n m d h1)). Qed.
Lemma lem1267000 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem1267002 (n : nat) (m : nat) : (Peano.le m n) = (term7 n m).
Proof. exact (EQ_MP (@lem1266968 n m) (@lem1266967 m n)). Qed.
Lemma lem1267003 (m : nat) (n : nat) : (Peano.le n m) = (term7 m n).
Proof. exact (@lem1267002 m n). Qed.
Lemma lem1267004 (n : nat) (m : nat) (h1 : Peano.le n m) : term7 m n.
Proof. exact (EQ_MP (@lem1267003 m n) (@lem1267000 n m h1)). Qed.
Lemma lem1267005 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : m = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem1267006 (x : nadd) (B : nat) (n : nat) : (term22 x B n) = (term22 x B n).
Proof. exact (eq_refl (term22 x B n)). Qed.
Lemma lem1267007 (x : nadd) (B : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term23 x B n m) = (term24 x B n d).
Proof. exact (MK_COMB (@lem1267006 x B n) (@lem1267005 m n d h1)). Qed.
Lemma lem1267008 (x : nadd) (B : nat) (d : nat) (n : nat) : (term24 x B n d) = (term25 x B d n).
Proof. exact (eq_refl (term24 x B n d)). Qed.
Lemma lem1267009 (x : nadd) (B : nat) (n : nat) (m : nat) : (term26 x B n m) = (term26 x B n m).
Proof. exact (eq_refl (term26 x B n m)). Qed.
Lemma lem1267010 (m : nat) (x : nadd) (B : nat) (d : nat) (n : nat) : ((term23 x B n m) = (term24 x B n d)) = ((term23 x B n m) = (term25 x B d n)).
Proof. exact (MK_COMB (@lem1267009 x B n m) (@lem1267008 x B d n)). Qed.
Lemma lem1267011 (x : nadd) (B : nat) (m : nat) (n : nat) : (term23 x B n m) = (term20 x B m n).
Proof. exact (eq_refl (term23 x B n m)). Qed.
Lemma lem1267012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1267013 (x : nadd) (B : nat) (m : nat) (n : nat) : (term26 x B n m) = (term21 x B m n).
Proof. exact (MK_COMB (@lem1267012) (@lem1267011 x B m n)). Qed.
Lemma lem1267014 (x : nadd) (B : nat) (d : nat) (n : nat) : (term25 x B d n) = (term25 x B d n).
Proof. exact (eq_refl (term25 x B d n)). Qed.
Lemma lem1267015 (m : nat) (x : nadd) (B : nat) (d : nat) (n : nat) : ((term23 x B n m) = (term25 x B d n)) = ((term20 x B m n) = (term25 x B d n)).
Proof. exact (MK_COMB (@lem1267013 x B m n) (@lem1267014 x B d n)). Qed.
Lemma lem1267016 (m : nat) (x : nadd) (B : nat) (d : nat) (n : nat) : ((term23 x B n m) = (term24 x B n d)) = ((term20 x B m n) = (term25 x B d n)).
Proof. exact (TRANS (@lem1267010 m x B d n) (@lem1267015 m x B d n)). Qed.
Lemma lem1267017 (x : nadd) (B : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term20 x B m n) = (term25 x B d n).
Proof. exact (EQ_MP (@lem1267016 m x B d n) (@lem1267007 x B m n d h1)). Qed.
Lemma lem1267018 (x : nadd) (B : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term25 x B d n) = (term20 x B m n).
Proof. exact (SYM (@lem1267017 x B m n d h1)). Qed.
Lemma lem1267020 (n : nat) (m : nat) : (term3 m n) = (term3 n m).
Proof. exact (EQ_MP (@lem1266962 n m) (@lem1266961 m n)). Qed.
Lemma lem1267021 (d : nat) (x : nadd) (m : nat) : (term27 x m d) = (term28 d x m).
Proof. exact (@lem1267020 (term29 x m d) (dest_nadd x m)). Qed.
Lemma lem1267022 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1267023 (d : nat) (x : nadd) (m : nat) : (term30 x m d) = (term31 d x m).
Proof. exact (MK_COMB (@lem1267022) (@lem1267021 d x m)). Qed.
Lemma lem1267025 (n : nat) (m : nat) : (term3 m n) = (term3 n m).
Proof. exact (EQ_MP (@lem1266962 n m) (@lem1266961 m n)). Qed.
Lemma lem1267026 (d : nat) (m : nat) : (term32 m d) = (term33 d m).
Proof. exact (@lem1267025 (Nat.add m d) m). Qed.
Lemma lem1267027 (B : nat) : (Nat.mul B) = (Nat.mul B).
Proof. exact (eq_refl (Nat.mul B)). Qed.
Lemma lem1267028 (B : nat) (d : nat) (m : nat) : (term34 B m d) = (term35 B d m).
Proof. exact (MK_COMB (@lem1267027 B) (@lem1267026 d m)). Qed.
Lemma lem1267029 (x : nadd) (B : nat) (d : nat) (m : nat) : (term18 x B m d) = (term25 x B d m).
Proof. exact (MK_COMB (@lem1267023 d x m) (@lem1267028 B d m)). Qed.
Lemma lem1267030 (x : nadd) (B : nat) (m : nat) (d : nat) : (term25 x B d m) = (term18 x B m d).
Proof. exact (SYM (@lem1267029 x B d m)). Qed.
Lemma lem1267031 (m : nat) : term36 m.
Proof. exact (@lem1245246 m). Qed.
Lemma lem1267032 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1267033 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem1267032 m) (@lem1267031 m)). Qed.
Lemma lem1267034 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem1267033 m n). Qed.
Lemma lem1267035 (m : nat) (n : nat) : (term38 m n) = ((term33 n m) = n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem1267037 (m : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term39 x B m.
Proof. exact (@lem1266981 x B h1 m). Qed.
Lemma lem1267038 (x : nadd) (m : nat) (B : nat) : (term39 x B m) = (term40 x m B).
Proof. exact (eq_refl (term39 x B m)). Qed.
Lemma lem1267039 (m : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term40 x m B.
Proof. exact (EQ_MP (@lem1267038 x m B) (@lem1267037 m x B h1)). Qed.
Lemma lem1267040 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term41 x m B n.
Proof. exact (@lem1267039 m x B h1 n). Qed.
Lemma lem1267041 (x : nadd) (m : nat) (B : nat) (n : nat) : (term41 x m B n) = (term42 x m B n).
Proof. exact (eq_refl (term41 x m B n)). Qed.
Lemma lem1267042 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term42 x m B n.
Proof. exact (EQ_MP (@lem1267041 x m B n) (@lem1267040 m n x B h1)). Qed.
Lemma lem1267043 (x : nadd) (m : nat) (B : nat) (n : nat) : (term42 x m B n) = ((term42 x m B n) = True).
Proof. exact (@lem7 (term42 x m B n)). Qed.
Lemma lem1267048 (m : nat) (n : nat) : (term33 n m) = n.
Proof. exact (EQ_MP (@lem1267035 m n) (@lem1267034 m n)). Qed.
Lemma lem1267049 (m : nat) (d : nat) : (term33 d m) = d.
Proof. exact (@lem1267048 m d). Qed.
Lemma lem1267050 (B : nat) : (Nat.mul B) = (Nat.mul B).
Proof. exact (eq_refl (Nat.mul B)). Qed.
Lemma lem1267051 (m : nat) (B : nat) (d : nat) : (term35 B d m) = (Nat.mul B d).
Proof. exact (MK_COMB (@lem1267050 B) (@lem1267049 m d)). Qed.
Lemma lem1267052 (d : nat) (x : nadd) (m : nat) : (term31 d x m) = (term31 d x m).
Proof. exact (eq_refl (term31 d x m)). Qed.
Lemma lem1267053 (x : nadd) (m : nat) (B : nat) (d : nat) : (term25 x B d m) = (term42 x m B d).
Proof. exact (MK_COMB (@lem1267052 d x m) (@lem1267051 m B d)). Qed.
Lemma lem1267055 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term14 x B) : (term42 x m B n) = True.
Proof. exact (EQ_MP (@lem1267043 x m B n) (@lem1267042 m n x B h1)). Qed.
Lemma lem1267056 (m : nat) (d : nat) (x : nadd) (B : nat) (h1 : term14 x B) : (term42 x m B d) = True.
Proof. exact (@lem1267055 m d x B h1). Qed.
Lemma lem1267057 (d : nat) (m : nat) (x : nadd) (B : nat) (h1 : term14 x B) : (term25 x B d m) = True.
Proof. exact (TRANS (@lem1267053 x m B d) (@lem1267056 m d x B h1)). Qed.
Lemma lem1267058 (d : nat) (m : nat) (x : nadd) (B : nat) (h1 : term14 x B) : True = (term25 x B d m).
Proof. exact (SYM (@lem1267057 d m x B h1)). Qed.
Lemma lem1267059 (d : nat) (m : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term25 x B d m.
Proof. exact (EQ_MP (@lem1267058 d m x B h1) (@lem0)). Qed.
Lemma lem1267060 (m : nat) : term36 m.
Proof. exact (@lem1245246 m). Qed.
Lemma lem1267061 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1267062 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem1267061 m) (@lem1267060 m)). Qed.
Lemma lem1267063 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem1267062 m n). Qed.
Lemma lem1267064 (m : nat) (n : nat) : (term38 m n) = ((term33 n m) = n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem1267066 (m : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term39 x B m.
Proof. exact (@lem1266981 x B h1 m). Qed.
Lemma lem1267067 (x : nadd) (m : nat) (B : nat) : (term39 x B m) = (term40 x m B).
Proof. exact (eq_refl (term39 x B m)). Qed.
Lemma lem1267068 (m : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term40 x m B.
Proof. exact (EQ_MP (@lem1267067 x m B) (@lem1267066 m x B h1)). Qed.
Lemma lem1267069 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term41 x m B n.
Proof. exact (@lem1267068 m x B h1 n). Qed.
Lemma lem1267070 (x : nadd) (m : nat) (B : nat) (n : nat) : (term41 x m B n) = (term42 x m B n).
Proof. exact (eq_refl (term41 x m B n)). Qed.
Lemma lem1267071 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term42 x m B n.
Proof. exact (EQ_MP (@lem1267070 x m B n) (@lem1267069 m n x B h1)). Qed.
Lemma lem1267072 (x : nadd) (m : nat) (B : nat) (n : nat) : (term42 x m B n) = ((term42 x m B n) = True).
Proof. exact (@lem7 (term42 x m B n)). Qed.
Lemma lem1267077 (m : nat) (n : nat) : (term33 n m) = n.
Proof. exact (EQ_MP (@lem1267064 m n) (@lem1267063 m n)). Qed.
Lemma lem1267078 (n : nat) (d : nat) : (term33 d n) = d.
Proof. exact (@lem1267077 n d). Qed.
Lemma lem1267079 (B : nat) : (Nat.mul B) = (Nat.mul B).
Proof. exact (eq_refl (Nat.mul B)). Qed.
Lemma lem1267080 (n : nat) (B : nat) (d : nat) : (term35 B d n) = (Nat.mul B d).
Proof. exact (MK_COMB (@lem1267079 B) (@lem1267078 n d)). Qed.
Lemma lem1267081 (d : nat) (x : nadd) (n : nat) : (term31 d x n) = (term31 d x n).
Proof. exact (eq_refl (term31 d x n)). Qed.
Lemma lem1267082 (x : nadd) (n : nat) (B : nat) (d : nat) : (term25 x B d n) = (term42 x n B d).
Proof. exact (MK_COMB (@lem1267081 d x n) (@lem1267080 n B d)). Qed.
Lemma lem1267084 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term14 x B) : (term42 x m B n) = True.
Proof. exact (EQ_MP (@lem1267072 x m B n) (@lem1267071 m n x B h1)). Qed.
Lemma lem1267085 (n : nat) (d : nat) (x : nadd) (B : nat) (h1 : term14 x B) : (term42 x n B d) = True.
Proof. exact (@lem1267084 n d x B h1). Qed.
Lemma lem1267086 (d : nat) (n : nat) (x : nadd) (B : nat) (h1 : term14 x B) : (term25 x B d n) = True.
Proof. exact (TRANS (@lem1267082 x n B d) (@lem1267085 n d x B h1)). Qed.
Lemma lem1267087 (d : nat) (n : nat) (x : nadd) (B : nat) (h1 : term14 x B) : True = (term25 x B d n).
Proof. exact (SYM (@lem1267086 d n x B h1)). Qed.
Lemma lem1267088 (d : nat) (n : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term25 x B d n.
Proof. exact (EQ_MP (@lem1267087 d n x B h1) (@lem0)). Qed.
Lemma lem1267089 (m : nat) (d : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term18 x B m d.
Proof. exact (EQ_MP (@lem1267030 x B m d) (@lem1267059 d m x B h1)). Qed.
Lemma lem1267090 (x : nadd) (B : nat) (m : nat) (n : nat) (d : nat) (h1 : term14 x B) (h2 : m = (Nat.add n d)) : term20 x B m n.
Proof. exact (EQ_MP (@lem1267018 x B m n d h2) (@lem1267088 d n x B h1)). Qed.
Lemma lem1267091 (x : nadd) (B : nat) (n : nat) (m : nat) (h1 : term14 x B) (h2 : Peano.le n m) : term20 x B m n.
Proof. exact (ex_elim (@lem1267004 n m h2) (fun d : nat => fun h0 : term43 m n d => @lem1267090 x B m n d h1 h0)). Qed.
Lemma lem1267092 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term44 x B m n.
Proof. exact (fun h0 : Peano.le n m => @lem1267091 x B n m h1 h0). Qed.
Lemma lem1267093 (x : nadd) (B : nat) (n : nat) (m : nat) (d : nat) (h1 : term14 x B) (h2 : n = (Nat.add m d)) : term20 x B m n.
Proof. exact (EQ_MP (@lem1266999 x B n m d h2) (@lem1267089 m d x B h1)). Qed.
Lemma lem1267094 (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : term14 x B) (h2 : Peano.le m n) : term20 x B m n.
Proof. exact (ex_elim (@lem1266985 m n h2) (fun d : nat => fun h0 : term43 n m d => @lem1267093 x B n m d h1 h0)). Qed.
Lemma lem1267095 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term45 x B m n.
Proof. exact (fun h0 : Peano.le m n => @lem1267094 x B m n h1 h0). Qed.
Lemma lem1267096 (x : nadd) (B : nat) (n : nat) (m : nat) (h1 : term14 x B) (h2 : Peano.le n m) : term20 x B m n.
Proof. exact (@lem1267092 m n x B h1 (@lem1266977 n m h2)). Qed.
Lemma lem1267097 (x : nadd) (B : nat) (m : nat) (n : nat) (h1 : term14 x B) (h2 : Peano.le m n) : term20 x B m n.
Proof. exact (@lem1267095 m n x B h1 (@lem1266976 m n h2)). Qed.
Lemma lem1267098 (m : nat) (n : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term20 x B m n.
Proof. exact (or_elim (@lem1266975 n m) (fun h0 : Peano.le m n => @lem1267097 x B m n h1 h0) (fun h0 : Peano.le n m => @lem1267096 x B n m h1 h0)). Qed.
Lemma lem1267103 (m : nat) (x : nadd) (B : nat) (h1 : term14 x B) : term46 x B m.
Proof. exact (fun n : nat => @lem1267098 m n x B h1). Qed.
Lemma lem1267108 (x : nadd) (B : nat) (h1 : term14 x B) : term47 x B.
Proof. exact (fun m : nat => @lem1267103 m x B h1). Qed.
Lemma lem1267109 (x : nadd) (B : nat) (h1 : term14 x B) : term48 x.
Proof. exact (ex_intro (term49 x) B (@lem1267108 x B h1)). Qed.
Lemma lem1267110 (x : nadd) : term48 x.
Proof. exact (ex_elim (@lem1266980 x) (fun B : nat => fun h0 : term50 x B => @lem1267109 x B h0)). Qed.
Lemma lem1267115 : term51.
Proof. exact (fun x : nadd => @lem1267110 x). Qed.

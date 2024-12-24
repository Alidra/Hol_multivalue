Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1253393_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1252926 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1252927 (m : nat) (n : nat) : (Nat.add n m) = (Nat.add m n).
Proof. exact (@lem1252926 m n). Qed.
Lemma lem1252930 (m : nat) (n : nat) : (term0 m n) = (term0 m n).
Proof. exact (eq_refl (term0 m n)). Qed.
Lemma lem1252931 (m : nat) (n : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add m n)).
Proof. exact (MK_COMB (@lem1252930 m n) (@lem1252927 m n)). Qed.
Lemma lem1252933 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1252934 (x : nat) : (x = x) = True.
Proof. exact (@lem1252933 nat x). Qed.
Lemma lem1252935 (m : nat) (n : nat) : ((Nat.add m n) = (Nat.add m n)) = True.
Proof. exact (@lem1252934 (Nat.add m n)). Qed.
Lemma lem1252936 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = True.
Proof. exact (TRANS (@lem1252931 m n) (@lem1252935 m n)). Qed.
Lemma lem1252937 (n : nat) (m : nat) : True = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (SYM (@lem1252936 n m)). Qed.
Lemma lem1252938 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1252937 n m) (@lem0)). Qed.
Lemma lem1252942 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1252943 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 m n d' d'' d''') = (term4 m n d' d'' d''').
Proof. exact (@lem1252942 (Nat.add m d') (Nat.add n d'') (term5 d' d'' d''')). Qed.
Lemma lem1252945 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1252946 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term4 m n d' d'' d''') = (term6 m n d' d'' d''').
Proof. exact (@lem1252945 m d' (term7 n d' d'' d''')). Qed.
Lemma lem1252948 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252949 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term6 m n d' d'' d''') = (term8 m n d' d'' d''').
Proof. exact (@lem1252948 d' m (term7 n d' d'' d''')). Qed.
Lemma lem1252956 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term4 m n d' d'' d''') = (term8 m n d' d'' d''').
Proof. exact (TRANS (@lem1252946 m n d' d'' d''') (@lem1252949 m n d' d'' d''')). Qed.
Lemma lem1252957 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 m n d' d'' d''') = (term8 m n d' d'' d''').
Proof. exact (TRANS (@lem1252943 m n d' d'' d''') (@lem1252956 m n d' d'' d''')). Qed.
Lemma lem1252965 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1252966 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term7 n d' d'' d''') = (term9 n d' d'' d''').
Proof. exact (@lem1252965 n d'' (term5 d' d'' d''')). Qed.
Lemma lem1252968 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252969 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term9 n d' d'' d''') = (term10 n d' d'' d''').
Proof. exact (@lem1252968 d'' n (term5 d' d'' d''')). Qed.
Lemma lem1252976 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term7 n d' d'' d''') = (term10 n d' d'' d''').
Proof. exact (TRANS (@lem1252966 n d' d'' d''') (@lem1252969 n d' d'' d''')). Qed.
Lemma lem1252984 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1252985 (d' : nat) (d'' : nat) (d''' : nat) : (term5 d' d'' d''') = (term11 d' d'' d''').
Proof. exact (@lem1252984 d' d'' (S d''')). Qed.
Lemma lem1252995 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1252996 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term12 n d' d'' d''') = (term13 n d' d'' d''').
Proof. exact (MK_COMB (@lem1252995 n) (@lem1252985 d' d'' d''')). Qed.
Lemma lem1252998 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252999 (d' : nat) (n : nat) (d'' : nat) (d''' : nat) : (term13 n d' d'' d''') = (term13 d' n d'' d''').
Proof. exact (@lem1252998 d' n (term14 d'' d''')). Qed.
Lemma lem1253007 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253008 (d'' : nat) (n : nat) (d''' : nat) : (term11 n d'' d''') = (term11 d'' n d''').
Proof. exact (@lem1253007 d'' n (S d''')). Qed.
Lemma lem1253018 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253019 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term13 d' n d'' d''') = (term13 d' d'' n d''').
Proof. exact (MK_COMB (@lem1253018 d') (@lem1253008 d'' n d''')). Qed.
Lemma lem1253026 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term13 n d' d'' d''') = (term13 d' d'' n d''').
Proof. exact (TRANS (@lem1252999 d' n d'' d''') (@lem1253019 d' d'' n d''')). Qed.
Lemma lem1253027 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term12 n d' d'' d''') = (term13 d' d'' n d''').
Proof. exact (TRANS (@lem1252996 n d' d'' d''') (@lem1253026 d' d'' n d''')). Qed.
Lemma lem1253028 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1253029 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term10 n d' d'' d''') = (term15 d' d'' n d''').
Proof. exact (MK_COMB (@lem1253028 d'') (@lem1253027 d' d'' n d''')). Qed.
Lemma lem1253031 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253032 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term15 d' d'' n d''') = (term16 d' d'' n d''').
Proof. exact (@lem1253031 d' d'' (term11 d'' n d''')). Qed.
Lemma lem1253054 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term10 n d' d'' d''') = (term16 d' d'' n d''').
Proof. exact (TRANS (@lem1253029 d' d'' n d''') (@lem1253032 d' d'' n d''')). Qed.
Lemma lem1253055 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term7 n d' d'' d''') = (term16 d' d'' n d''').
Proof. exact (TRANS (@lem1252976 n d' d'' d''') (@lem1253054 d' d'' n d''')). Qed.
Lemma lem1253056 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1253057 (m : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term17 m n d' d'' d''') = (term18 m d' d'' n d''').
Proof. exact (MK_COMB (@lem1253056 m) (@lem1253055 d' d'' n d''')). Qed.
Lemma lem1253059 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253060 (d' : nat) (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term18 m d' d'' n d''') = (term18 d' m d'' n d''').
Proof. exact (@lem1253059 d' m (term19 d'' n d''')). Qed.
Lemma lem1253068 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253069 (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term16 m d'' n d''') = (term15 m d'' n d''').
Proof. exact (@lem1253068 d'' m (term11 d'' n d''')). Qed.
Lemma lem1253077 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253078 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term13 m d'' n d''') = (term13 d'' m n d''').
Proof. exact (@lem1253077 d'' m (term14 n d''')). Qed.
Lemma lem1253094 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1253095 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term15 m d'' n d''') = (term20 d'' m n d''').
Proof. exact (MK_COMB (@lem1253094 d'') (@lem1253078 d'' m n d''')). Qed.
Lemma lem1253102 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term16 m d'' n d''') = (term20 d'' m n d''').
Proof. exact (TRANS (@lem1253069 m d'' n d''') (@lem1253095 d'' m n d''')). Qed.
Lemma lem1253103 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253104 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term18 d' m d'' n d''') = (term21 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1253103 d') (@lem1253102 d'' m n d''')). Qed.
Lemma lem1253111 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term18 m d' d'' n d''') = (term21 d' d'' m n d''').
Proof. exact (TRANS (@lem1253060 d' m d'' n d''') (@lem1253104 d' d'' m n d''')). Qed.
Lemma lem1253112 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term17 m n d' d'' d''') = (term21 d' d'' m n d''').
Proof. exact (TRANS (@lem1253057 m d' d'' n d''') (@lem1253111 d' d'' m n d''')). Qed.
Lemma lem1253113 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253114 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term8 m n d' d'' d''') = (term22 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1253113 d') (@lem1253112 d' d'' m n d''')). Qed.
Lemma lem1253121 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term3 m n d' d'' d''') = (term22 d' d'' m n d''').
Proof. exact (TRANS (@lem1252957 m n d' d'' d''') (@lem1253114 d' d'' m n d''')). Qed.
Lemma lem1253122 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1253123 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term23 m n d' d'' d''') = (term24 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1253122) (@lem1253121 d' d'' m n d''')). Qed.
Lemma lem1253125 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253126 (m : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term25 n m d'' d' d''') = (term25 m n d'' d' d''').
Proof. exact (@lem1253125 m n (term26 d'' d' d''')). Qed.
Lemma lem1253134 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253135 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term27 n d'' d' d''') = (term28 n d'' d' d''').
Proof. exact (@lem1253134 d'' n (term29 d'' d' d''')). Qed.
Lemma lem1253143 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253144 (d'' : nat) (n : nat) (d' : nat) (d''' : nat) : (term30 n d'' d' d''') = (term30 d'' n d' d''').
Proof. exact (@lem1253143 d'' n (term31 d' d''')). Qed.
Lemma lem1253152 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253153 (n : nat) (d' : nat) (d''' : nat) : (term29 n d' d''') = (term32 n d' d''').
Proof. exact (@lem1253152 d' n (term14 d' d''')). Qed.
Lemma lem1253161 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253162 (d' : nat) (n : nat) (d''' : nat) : (term11 n d' d''') = (term11 d' n d''').
Proof. exact (@lem1253161 d' n (S d''')). Qed.
Lemma lem1253172 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253173 (d' : nat) (n : nat) (d''' : nat) : (term32 n d' d''') = (term19 d' n d''').
Proof. exact (MK_COMB (@lem1253172 d') (@lem1253162 d' n d''')). Qed.
Lemma lem1253180 (d' : nat) (n : nat) (d''' : nat) : (term29 n d' d''') = (term19 d' n d''').
Proof. exact (TRANS (@lem1253153 n d' d''') (@lem1253173 d' n d''')). Qed.
Lemma lem1253181 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1253182 (d'' : nat) (d' : nat) (n : nat) (d''' : nat) : (term30 d'' n d' d''') = (term16 d'' d' n d''').
Proof. exact (MK_COMB (@lem1253181 d'') (@lem1253180 d' n d''')). Qed.
Lemma lem1253184 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253185 (d'' : nat) (d' : nat) (n : nat) (d''' : nat) : (term16 d'' d' n d''') = (term15 d'' d' n d''').
Proof. exact (@lem1253184 d' d'' (term11 d' n d''')). Qed.
Lemma lem1253193 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253194 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term13 d'' d' n d''') = (term13 d' d'' n d''').
Proof. exact (@lem1253193 d' d'' (term14 n d''')). Qed.
Lemma lem1253210 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253211 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term15 d'' d' n d''') = (term20 d' d'' n d''').
Proof. exact (MK_COMB (@lem1253210 d') (@lem1253194 d' d'' n d''')). Qed.
Lemma lem1253218 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term16 d'' d' n d''') = (term20 d' d'' n d''').
Proof. exact (TRANS (@lem1253185 d'' d' n d''') (@lem1253211 d' d'' n d''')). Qed.
Lemma lem1253219 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term30 d'' n d' d''') = (term20 d' d'' n d''').
Proof. exact (TRANS (@lem1253182 d'' d' n d''') (@lem1253218 d' d'' n d''')). Qed.
Lemma lem1253220 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term30 n d'' d' d''') = (term20 d' d'' n d''').
Proof. exact (TRANS (@lem1253144 d'' n d' d''') (@lem1253219 d' d'' n d''')). Qed.
Lemma lem1253221 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1253222 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term28 n d'' d' d''') = (term33 d' d'' n d''').
Proof. exact (MK_COMB (@lem1253221 d'') (@lem1253220 d' d'' n d''')). Qed.
Lemma lem1253224 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253225 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term33 d' d'' n d''') = (term34 d' d'' n d''').
Proof. exact (@lem1253224 d' d'' (term13 d' d'' n d''')). Qed.
Lemma lem1253233 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253234 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term15 d' d'' n d''') = (term16 d' d'' n d''').
Proof. exact (@lem1253233 d' d'' (term11 d'' n d''')). Qed.
Lemma lem1253256 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253257 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term34 d' d'' n d''') = (term35 d' d'' n d''').
Proof. exact (MK_COMB (@lem1253256 d') (@lem1253234 d' d'' n d''')). Qed.
Lemma lem1253264 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term33 d' d'' n d''') = (term35 d' d'' n d''').
Proof. exact (TRANS (@lem1253225 d' d'' n d''') (@lem1253257 d' d'' n d''')). Qed.
Lemma lem1253265 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term28 n d'' d' d''') = (term35 d' d'' n d''').
Proof. exact (TRANS (@lem1253222 d' d'' n d''') (@lem1253264 d' d'' n d''')). Qed.
Lemma lem1253266 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term27 n d'' d' d''') = (term35 d' d'' n d''').
Proof. exact (TRANS (@lem1253135 n d'' d' d''') (@lem1253265 d' d'' n d''')). Qed.
Lemma lem1253267 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1253268 (m : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term25 m n d'' d' d''') = (term36 m d' d'' n d''').
Proof. exact (MK_COMB (@lem1253267 m) (@lem1253266 d' d'' n d''')). Qed.
Lemma lem1253270 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253271 (m : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term36 m d' d'' n d''') = (term37 m d' d'' n d''').
Proof. exact (@lem1253270 d' m (term16 d' d'' n d''')). Qed.
Lemma lem1253279 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253280 (d' : nat) (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term18 m d' d'' n d''') = (term18 d' m d'' n d''').
Proof. exact (@lem1253279 d' m (term19 d'' n d''')). Qed.
Lemma lem1253288 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253289 (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term16 m d'' n d''') = (term15 m d'' n d''').
Proof. exact (@lem1253288 d'' m (term11 d'' n d''')). Qed.
Lemma lem1253297 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1253298 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term13 m d'' n d''') = (term13 d'' m n d''').
Proof. exact (@lem1253297 d'' m (term14 n d''')). Qed.
Lemma lem1253314 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1253315 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term15 m d'' n d''') = (term20 d'' m n d''').
Proof. exact (MK_COMB (@lem1253314 d'') (@lem1253298 d'' m n d''')). Qed.
Lemma lem1253322 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term16 m d'' n d''') = (term20 d'' m n d''').
Proof. exact (TRANS (@lem1253289 m d'' n d''') (@lem1253315 d'' m n d''')). Qed.
Lemma lem1253323 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253324 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term18 d' m d'' n d''') = (term21 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1253323 d') (@lem1253322 d'' m n d''')). Qed.
Lemma lem1253331 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term18 m d' d'' n d''') = (term21 d' d'' m n d''').
Proof. exact (TRANS (@lem1253280 d' m d'' n d''') (@lem1253324 d' d'' m n d''')). Qed.
Lemma lem1253332 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1253333 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term37 m d' d'' n d''') = (term22 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1253332 d') (@lem1253331 d' d'' m n d''')). Qed.
Lemma lem1253340 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term36 m d' d'' n d''') = (term22 d' d'' m n d''').
Proof. exact (TRANS (@lem1253271 m d' d'' n d''') (@lem1253333 d' d'' m n d''')). Qed.
Lemma lem1253341 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term25 m n d'' d' d''') = (term22 d' d'' m n d''').
Proof. exact (TRANS (@lem1253268 m d' d'' n d''') (@lem1253340 d' d'' m n d''')). Qed.
Lemma lem1253342 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term25 n m d'' d' d''') = (term22 d' d'' m n d''').
Proof. exact (TRANS (@lem1253126 m n d'' d' d''') (@lem1253341 d' d'' m n d''')). Qed.
Lemma lem1253343 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : ((term3 m n d' d'' d''') = (term25 n m d'' d' d''')) = ((term22 d' d'' m n d''') = (term22 d' d'' m n d''')).
Proof. exact (MK_COMB (@lem1253123 d' d'' m n d''') (@lem1253342 d' d'' m n d''')). Qed.
Lemma lem1253345 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1253346 (x : nat) : (x = x) = True.
Proof. exact (@lem1253345 nat x). Qed.
Lemma lem1253347 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : ((term22 d' d'' m n d''') = (term22 d' d'' m n d''')) = True.
Proof. exact (@lem1253346 (term22 d' d'' m n d''')). Qed.
Lemma lem1253348 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term3 m n d' d'' d''') = (term25 n m d'' d' d''')) = True.
Proof. exact (TRANS (@lem1253343 d' d'' m n d''') (@lem1253347 d' d'' m n d''')). Qed.
Lemma lem1253349 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term3 m n d' d'' d''') = (term25 n m d'' d' d''')).
Proof. exact (SYM (@lem1253348 n m d'' d' d''')). Qed.
Lemma lem1253350 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term3 m n d' d'' d''') = (term25 n m d'' d' d''').
Proof. exact (EQ_MP (@lem1253349 n m d'' d' d''') (@lem0)). Qed.
Lemma lem1253351 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1253352 (n : nat) (m : nat) : (term0 m n) = (term0 n m).
Proof. exact (MK_COMB (@lem1253351) (@lem1252938 n m)). Qed.
Lemma lem1253353 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add m n) = (term3 m n d' d'' d''')) = ((Nat.add n m) = (term25 n m d'' d' d''')).
Proof. exact (MK_COMB (@lem1253352 n m) (@lem1253350 n m d'' d' d''')). Qed.
Lemma lem1253354 (m : nat) : term38 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1253355 (m : nat) : (term38 m) = (term39 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem1253356 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem1253355 m) (@lem1253354 m)). Qed.
Lemma lem1253357 (m : nat) (n : nat) : term40 m n.
Proof. exact (@lem1253356 m n). Qed.
Lemma lem1253358 (m : nat) (n : nat) : (term40 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem1253366 (m : nat) : term41 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1253367 (m : nat) : (term41 m) = (term42 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem1253368 (m : nat) : term42 m.
Proof. exact (EQ_MP (@lem1253367 m) (@lem1253366 m)). Qed.
Lemma lem1253369 (m : nat) (n : nat) : term43 m n.
Proof. exact (@lem1253368 m n). Qed.
Lemma lem1253370 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem1253371 (m : nat) (n : nat) : term44 m n.
Proof. exact (EQ_MP (@lem1253370 m n) (@lem1253369 m n)). Qed.
Lemma lem1253372 (m : nat) (n : nat) (p : nat) : term45 m n p.
Proof. exact (@lem1253371 m n p). Qed.
Lemma lem1253373 (m : nat) (n : nat) (p : nat) : (term45 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term45 m n p)). Qed.
Lemma lem1253376 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1253373 m n p) (@lem1253372 m n p)). Qed.
Lemma lem1253377 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add n m) = (term25 n m d'' d' d''')) = (m = (term27 m d'' d' d''')).
Proof. exact (@lem1253376 n m (term27 m d'' d' d''')). Qed.
Lemma lem1253379 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1253358 m n) (@lem1253357 m n)). Qed.
Lemma lem1253384 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : (m = (term27 m d'' d' d''')) = ((term26 d'' d' d''') = (NUMERAL 0)).
Proof. exact (@lem1253379 m (term26 d'' d' d''')). Qed.
Lemma lem1253385 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add n m) = (term25 n m d'' d' d''')) = ((term26 d'' d' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1253377 n m d'' d' d''') (@lem1253384 m d'' d' d''')). Qed.
Lemma lem1253386 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term46 m n d' d'' d''') = (term46 m n d' d'' d''').
Proof. exact (eq_refl (term46 m n d' d'' d''')). Qed.
Lemma lem1253387 (m : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (((Nat.add m n) = (term3 m n d' d'' d''')) = ((Nat.add n m) = (term25 n m d'' d' d'''))) = (((Nat.add m n) = (term3 m n d' d'' d''')) = ((term26 d'' d' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1253386 m n d' d'' d''') (@lem1253385 n m d'' d' d''')). Qed.
Lemma lem1253388 (m : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add m n) = (term3 m n d' d'' d''')) = ((term26 d'' d' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1253387 m n d'' d' d''') (@lem1253353 n m d'' d' d''')). Qed.
Lemma lem1253389 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1253390 (m : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term47 m n d' d'' d''') = (term48 d'' d' d''').
Proof. exact (MK_COMB (@lem1253389) (@lem1253388 m n d'' d' d''')). Qed.
Lemma lem1253391 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1253392 (m : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term49 m n d' d'' d''') = (term50 d'' d' d''').
Proof. exact (MK_COMB (@lem1253390 m n d'' d' d''') (@lem1253391)). Qed.
Lemma lem1253393 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term50 d'' d' d''') = (term49 m n d' d'' d''').
Proof. exact (SYM (@lem1253392 m n d'' d' d''')). Qed.

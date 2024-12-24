Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LENGTH_LIST_OF_SEQ_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import LENGTH_APPEND_spec.
Require Import thm0_spec.
Require Import thm1097080_spec.
Require Import thm1111460_spec.
Require Import thm1111461_spec.
Require Import thm1111466_spec.
Require Import thm1111467_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1236913 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1236914 {A : Type'} (s : nat -> A) : term1 A s.
Proof. exact (@lem1236913 (term2 A s)). Qed.
Lemma lem1236915 {A : Type'} (s : nat -> A) : (term3 A s) = ((term4 A s) = (NUMERAL 0)).
Proof. exact (eq_refl (term3 A s)). Qed.
Lemma lem1236916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1236917 {A : Type'} (s : nat -> A) : (term5 A s) = (term6 A s).
Proof. exact (MK_COMB (@lem1236916) (@lem1236915 A s)). Qed.
Lemma lem1236918 {A : Type'} (s : nat -> A) (n : nat) : (term7 A s n) = ((term8 A s n) = n).
Proof. exact (eq_refl (term7 A s n)). Qed.
Lemma lem1236919 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1236920 {A : Type'} (s : nat -> A) (n : nat) : (term9 A s n) = (term10 A s n).
Proof. exact (MK_COMB (@lem1236919) (@lem1236918 A s n)). Qed.
Lemma lem1236921 {A : Type'} (s : nat -> A) (n : nat) : (term11 A s n) = ((term12 A s n) = (S n)).
Proof. exact (eq_refl (term11 A s n)). Qed.
Lemma lem1236922 {A : Type'} (s : nat -> A) (n : nat) : (term13 A s n) = (term14 A s n).
Proof. exact (MK_COMB (@lem1236920 A s n) (@lem1236921 A s n)). Qed.
Lemma lem1236923 {A : Type'} (s : nat -> A) : (term15 A s) = (term16 A s).
Proof. exact (fun_ext (fun n : nat => @lem1236922 A s n)). Qed.
Lemma lem1236924 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1236925 {A : Type'} (s : nat -> A) : (term17 A s) = (term18 A s).
Proof. exact (MK_COMB (@lem1236924) (@lem1236923 A s)). Qed.
Lemma lem1236926 {A : Type'} (s : nat -> A) : (term19 A s) = (term20 A s).
Proof. exact (MK_COMB (@lem1236917 A s) (@lem1236925 A s)). Qed.
Lemma lem1236927 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1236928 {A : Type'} (s : nat -> A) : (term21 A s) = (term22 A s).
Proof. exact (MK_COMB (@lem1236927) (@lem1236926 A s)). Qed.
Lemma lem1236929 {A : Type'} (s : nat -> A) (n : nat) : (term7 A s n) = ((term8 A s n) = n).
Proof. exact (eq_refl (term7 A s n)). Qed.
Lemma lem1236930 {A : Type'} (s : nat -> A) : (term23 A s) = (term2 A s).
Proof. exact (fun_ext (fun n : nat => @lem1236929 A s n)). Qed.
Lemma lem1236931 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1236932 {A : Type'} (s : nat -> A) : (term24 A s) = (term25 A s).
Proof. exact (MK_COMB (@lem1236931) (@lem1236930 A s)). Qed.
Lemma lem1236933 {A : Type'} (s : nat -> A) : (term1 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem1236928 A s) (@lem1236932 A s)). Qed.
Lemma lem1236934 {A : Type'} (s : nat -> A) : term26 A s.
Proof. exact (EQ_MP (@lem1236933 A s) (@lem1236914 A s)). Qed.
Lemma lem1236979 {A : Type'} (s : nat -> A) : (term27 A s) = (@nil A).
Proof. exact (EQ_MP (@lem1111461 A s) (@lem1111460 A s)). Qed.
Lemma lem1236980 {A : Type'} (s : nat -> A) : (term27 A s) = (@nil A).
Proof. exact (@lem1236979 A s). Qed.
Lemma lem1236981 {A : Type'} : (@List.length A) = (@List.length A).
Proof. exact (eq_refl (@List.length A)). Qed.
Lemma lem1236982 {A : Type'} (s : nat -> A) : (term4 A s) = (@List.length A (@nil A)).
Proof. exact (MK_COMB (@lem1236981 A) (@lem1236980 A s)). Qed.
Lemma lem1236984 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1236985 {A : Type'} (s : nat -> A) : (term4 A s) = (NUMERAL 0).
Proof. exact (TRANS (@lem1236982 A s) (@lem1236984 A)). Qed.
Lemma lem1236986 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1236987 {A : Type'} (s : nat -> A) : (term28 A s) = term29.
Proof. exact (MK_COMB (@lem1236986) (@lem1236985 A s)). Qed.
Lemma lem1236988 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1236989 {A : Type'} (s : nat -> A) : ((term4 A s) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1236987 A s) (@lem1236988)). Qed.
Lemma lem1236991 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1236992 (x : nat) : (x = x) = True.
Proof. exact (@lem1236991 nat x). Qed.
Lemma lem1236993 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1236992 (NUMERAL 0)). Qed.
Lemma lem1236994 {A : Type'} (s : nat -> A) : ((term4 A s) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1236989 A s) (@lem1236993)). Qed.
Lemma lem1236995 {A : Type'} (s : nat -> A) : True = ((term4 A s) = (NUMERAL 0)).
Proof. exact (SYM (@lem1236994 A s)). Qed.
Lemma lem1236996 {A : Type'} (s : nat -> A) : (term4 A s) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1236995 A s) (@lem0)). Qed.
Lemma lem1236997 : term30.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1236998 : term31.
Proof. exact (proj2 (@lem1236997)). Qed.
Lemma lem1236999 : term32.
Proof. exact (proj2 (@lem1236998)). Qed.
Lemma lem1237000 (m : nat) : term33 m.
Proof. exact (@lem1236999 m). Qed.
Lemma lem1237001 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem1237002 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem1237001 m) (@lem1237000 m)). Qed.
Lemma lem1237003 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem1237002 m n). Qed.
Lemma lem1237004 (m : nat) (n : nat) : (term35 m n) = ((term36 m n) = (term37 m n)).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1237013 : term38.
Proof. exact (proj1 (@lem1236997)). Qed.
Lemma lem1237014 (m : nat) : term39 m.
Proof. exact (@lem1237013 m). Qed.
Lemma lem1237015 (m : nat) : (term39 m) = ((term40 m) = m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem1237021 {A : Type'} (l : list A) : term41 A l.
Proof. exact (@lem1116558 A l). Qed.
Lemma lem1237022 {A : Type'} (l : list A) : (term41 A l) = (term42 A l).
Proof. exact (eq_refl (term41 A l)). Qed.
Lemma lem1237023 {A : Type'} (l : list A) : term42 A l.
Proof. exact (EQ_MP (@lem1237022 A l) (@lem1237021 A l)). Qed.
Lemma lem1237024 {A : Type'} (l : list A) (m : list A) : term43 A l m.
Proof. exact (@lem1237023 A l m). Qed.
Lemma lem1237025 {A : Type'} (l : list A) (m : list A) : (term43 A l m) = ((term44 A l m) = (term45 A l m)).
Proof. exact (eq_refl (term43 A l m)). Qed.
Lemma lem1237027 {A : Type'} : term46 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1237028 {A : Type'} (h : A) : term47 A h.
Proof. exact (@lem1237027 A h). Qed.
Lemma lem1237029 {A : Type'} (h : A) : (term47 A h) = (term48 A h).
Proof. exact (eq_refl (term47 A h)). Qed.
Lemma lem1237030 {A : Type'} (h : A) : term48 A h.
Proof. exact (EQ_MP (@lem1237029 A h) (@lem1237028 A h)). Qed.
Lemma lem1237031 {A : Type'} (h : A) (t : list A) : term49 A h t.
Proof. exact (@lem1237030 A h t). Qed.
Lemma lem1237032 {A : Type'} (h : A) (t : list A) : (term49 A h t) = ((term50 A h t) = (term51 A t)).
Proof. exact (eq_refl (term49 A h t)). Qed.
Lemma lem1237040 {A : Type'} (s : nat -> A) (n : nat) : (term52 A s n) = (term53 A s n).
Proof. exact (EQ_MP (@lem1111467 A s n) (@lem1111466 A s n)). Qed.
Lemma lem1237041 {A : Type'} (s : nat -> A) (n : nat) : (term52 A s n) = (term53 A s n).
Proof. exact (@lem1237040 A s n). Qed.
Lemma lem1237042 {A : Type'} : (@List.length A) = (@List.length A).
Proof. exact (eq_refl (@List.length A)). Qed.
Lemma lem1237043 {A : Type'} (s : nat -> A) (n : nat) : (term12 A s n) = (term54 A s n).
Proof. exact (MK_COMB (@lem1237042 A) (@lem1237041 A s n)). Qed.
Lemma lem1237045 {A : Type'} (l : list A) (m : list A) : (term44 A l m) = (term45 A l m).
Proof. exact (EQ_MP (@lem1237025 A l m) (@lem1237024 A l m)). Qed.
Lemma lem1237046 {A : Type'} (l : list A) (m : list A) : (term44 A l m) = (term45 A l m).
Proof. exact (@lem1237045 A l m). Qed.
Lemma lem1237047 {A : Type'} (s : nat -> A) (n : nat) : (term54 A s n) = (term55 A s n).
Proof. exact (@lem1237046 A (@list_of_seq A s n) (term56 A s n)). Qed.
Lemma lem1237049 {A : Type'} (s : nat -> A) (n : nat) (h1 : (term8 A s n) = n) : (term8 A s n) = n.
Proof. exact (h1). Qed.
Lemma lem1237050 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1237051 {A : Type'} (s : nat -> A) (n : nat) (h1 : (term8 A s n) = n) : (term57 A s n) = (Nat.add n).
Proof. exact (MK_COMB (@lem1237050) (@lem1237049 A s n h1)). Qed.
Lemma lem1237053 {A : Type'} (h : A) (t : list A) : (term50 A h t) = (term51 A t).
Proof. exact (EQ_MP (@lem1237032 A h t) (@lem1237031 A h t)). Qed.
Lemma lem1237054 {A : Type'} (h : A) (t : list A) : (term50 A h t) = (term51 A t).
Proof. exact (@lem1237053 A h t). Qed.
Lemma lem1237055 {A : Type'} (s : nat -> A) (n : nat) : (term58 A s n) = (term59 A).
Proof. exact (@lem1237054 A (s n) (@nil A)). Qed.
Lemma lem1237057 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1237058 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1237059 {A : Type'} : (term59 A) = term60.
Proof. exact (MK_COMB (@lem1237058) (@lem1237057 A)). Qed.
Lemma lem1237060 {A : Type'} (s : nat -> A) (n : nat) : (term58 A s n) = term60.
Proof. exact (TRANS (@lem1237055 A s n) (@lem1237059 A)). Qed.
Lemma lem1237061 {A : Type'} (s : nat -> A) (n : nat) (h1 : (term8 A s n) = n) : (term55 A s n) = (term61 n).
Proof. exact (MK_COMB (@lem1237051 A s n h1) (@lem1237060 A s n)). Qed.
Lemma lem1237063 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (EQ_MP (@lem1237004 m n) (@lem1237003 m n)). Qed.
Lemma lem1237064 (n : nat) : (term61 n) = (term62 n).
Proof. exact (@lem1237063 n (NUMERAL 0)). Qed.
Lemma lem1237066 (m : nat) : (term40 m) = m.
Proof. exact (EQ_MP (@lem1237015 m) (@lem1237014 m)). Qed.
Lemma lem1237067 (n : nat) : (term40 n) = n.
Proof. exact (@lem1237066 n). Qed.
Lemma lem1237068 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1237069 (n : nat) : (term62 n) = (S n).
Proof. exact (MK_COMB (@lem1237068) (@lem1237067 n)). Qed.
Lemma lem1237070 (n : nat) : (term61 n) = (S n).
Proof. exact (TRANS (@lem1237064 n) (@lem1237069 n)). Qed.
Lemma lem1237071 {A : Type'} (s : nat -> A) (n : nat) (h1 : (term8 A s n) = n) : (term55 A s n) = (S n).
Proof. exact (TRANS (@lem1237061 A s n h1) (@lem1237070 n)). Qed.
Lemma lem1237072 {A : Type'} (s : nat -> A) (n : nat) (h1 : (term8 A s n) = n) : (term54 A s n) = (S n).
Proof. exact (TRANS (@lem1237047 A s n) (@lem1237071 A s n h1)). Qed.
Lemma lem1237073 {A : Type'} (s : nat -> A) (n : nat) (h1 : (term8 A s n) = n) : (term12 A s n) = (S n).
Proof. exact (TRANS (@lem1237043 A s n) (@lem1237072 A s n h1)). Qed.
Lemma lem1237074 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1237075 {A : Type'} (s : nat -> A) (n : nat) (h1 : (term8 A s n) = n) : (term63 A s n) = (term64 n).
Proof. exact (MK_COMB (@lem1237074) (@lem1237073 A s n h1)). Qed.
Lemma lem1237076 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1237077 {A : Type'} (s : nat -> A) (n : nat) (h1 : (term8 A s n) = n) : ((term12 A s n) = (S n)) = ((S n) = (S n)).
Proof. exact (MK_COMB (@lem1237075 A s n h1) (@lem1237076 n)). Qed.
Lemma lem1237079 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1237080 (x : nat) : (x = x) = True.
Proof. exact (@lem1237079 nat x). Qed.
Lemma lem1237081 (n : nat) : ((S n) = (S n)) = True.
Proof. exact (@lem1237080 (S n)). Qed.
Lemma lem1237082 {A : Type'} (s : nat -> A) (n : nat) (h1 : (term8 A s n) = n) : ((term12 A s n) = (S n)) = True.
Proof. exact (TRANS (@lem1237077 A s n h1) (@lem1237081 n)). Qed.
Lemma lem1237083 {A : Type'} (s : nat -> A) (n : nat) (h1 : (term8 A s n) = n) : True = ((term12 A s n) = (S n)).
Proof. exact (SYM (@lem1237082 A s n h1)). Qed.
Lemma lem1237084 {A : Type'} (s : nat -> A) (n : nat) (h1 : (term8 A s n) = n) : (term12 A s n) = (S n).
Proof. exact (EQ_MP (@lem1237083 A s n h1) (@lem0)). Qed.
Lemma lem1237085 {A : Type'} (s : nat -> A) (n : nat) : term14 A s n.
Proof. exact (fun h0 : (term8 A s n) = n => @lem1237084 A s n h0). Qed.
Lemma lem1237090 {A : Type'} (s : nat -> A) : term18 A s.
Proof. exact (fun n : nat => @lem1237085 A s n). Qed.
Lemma lem1237091 {A : Type'} (s : nat -> A) : term20 A s.
Proof. exact (conj (@lem1236996 A s) (@lem1237090 A s)). Qed.
Lemma lem1237092 {A : Type'} (s : nat -> A) : term25 A s.
Proof. exact (@lem1236934 A s (@lem1237091 A s)). Qed.
Lemma lem1237097 {A : Type'} : term65 A.
Proof. exact (fun s : nat -> A => @lem1237092 A s). Qed.

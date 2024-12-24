Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1250093_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_LCANCEL_0_spec.
Require Import thm0_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1249863 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1249864 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term2 n d' d'' d''') = (term3 n d' d'' d''').
Proof. exact (@lem1249863 n d'' (term4 d' d'' d''')). Qed.
Lemma lem1249866 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249867 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 n d' d'' d''') = (term5 n d' d'' d''').
Proof. exact (@lem1249866 d'' n (term4 d' d'' d''')). Qed.
Lemma lem1249874 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term2 n d' d'' d''') = (term5 n d' d'' d''').
Proof. exact (TRANS (@lem1249864 n d' d'' d''') (@lem1249867 n d' d'' d''')). Qed.
Lemma lem1249882 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1249883 (d' : nat) (d'' : nat) (d''' : nat) : (term4 d' d'' d''') = (term6 d' d'' d''').
Proof. exact (@lem1249882 d' d'' (S d''')). Qed.
Lemma lem1249893 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1249894 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term7 n d' d'' d''') = (term8 n d' d'' d''').
Proof. exact (MK_COMB (@lem1249893 n) (@lem1249883 d' d'' d''')). Qed.
Lemma lem1249896 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249897 (d' : nat) (n : nat) (d'' : nat) (d''' : nat) : (term8 n d' d'' d''') = (term8 d' n d'' d''').
Proof. exact (@lem1249896 d' n (term9 d'' d''')). Qed.
Lemma lem1249905 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249906 (d'' : nat) (n : nat) (d''' : nat) : (term6 n d'' d''') = (term6 d'' n d''').
Proof. exact (@lem1249905 d'' n (S d''')). Qed.
Lemma lem1249916 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1249917 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term8 d' n d'' d''') = (term8 d' d'' n d''').
Proof. exact (MK_COMB (@lem1249916 d') (@lem1249906 d'' n d''')). Qed.
Lemma lem1249924 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term8 n d' d'' d''') = (term8 d' d'' n d''').
Proof. exact (TRANS (@lem1249897 d' n d'' d''') (@lem1249917 d' d'' n d''')). Qed.
Lemma lem1249925 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term7 n d' d'' d''') = (term8 d' d'' n d''').
Proof. exact (TRANS (@lem1249894 n d' d'' d''') (@lem1249924 d' d'' n d''')). Qed.
Lemma lem1249926 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1249927 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term5 n d' d'' d''') = (term10 d' d'' n d''').
Proof. exact (MK_COMB (@lem1249926 d'') (@lem1249925 d' d'' n d''')). Qed.
Lemma lem1249929 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249930 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term10 d' d'' n d''') = (term11 d' d'' n d''').
Proof. exact (@lem1249929 d' d'' (term6 d'' n d''')). Qed.
Lemma lem1249952 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term5 n d' d'' d''') = (term11 d' d'' n d''').
Proof. exact (TRANS (@lem1249927 d' d'' n d''') (@lem1249930 d' d'' n d''')). Qed.
Lemma lem1249953 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term2 n d' d'' d''') = (term11 d' d'' n d''').
Proof. exact (TRANS (@lem1249874 n d' d'' d''') (@lem1249952 d' d'' n d''')). Qed.
Lemma lem1249954 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1249955 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term12 n d' d'' d''') = (term13 d' d'' n d''').
Proof. exact (MK_COMB (@lem1249954) (@lem1249953 d' d'' n d''')). Qed.
Lemma lem1249957 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249958 (d' : nat) (n : nat) (d''' : nat) (d'' : nat) : (term14 n d' d''' d'') = (term14 d' n d''' d'').
Proof. exact (@lem1249957 d' n (term15 d''' d'')). Qed.
Lemma lem1249972 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249973 (d''' : nat) (d'' : nat) : (term15 d''' d'') = (term16 d''' d'').
Proof. exact (@lem1249972 d'' (S d''') d''). Qed.
Lemma lem1249981 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1249982 (d'' : nat) (d''' : nat) : (term17 d''' d'') = (term9 d'' d''').
Proof. exact (@lem1249981 d'' (S d''')). Qed.
Lemma lem1249986 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1249987 (d'' : nat) (d''' : nat) : (term16 d''' d'') = (term18 d'' d''').
Proof. exact (MK_COMB (@lem1249986 d'') (@lem1249982 d'' d''')). Qed.
Lemma lem1249994 (d'' : nat) (d''' : nat) : (term15 d''' d'') = (term18 d'' d''').
Proof. exact (TRANS (@lem1249973 d''' d'') (@lem1249987 d'' d''')). Qed.
Lemma lem1249995 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1249996 (n : nat) (d'' : nat) (d''' : nat) : (term19 n d''' d'') = (term20 n d'' d''').
Proof. exact (MK_COMB (@lem1249995 n) (@lem1249994 d'' d''')). Qed.
Lemma lem1249998 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249999 (n : nat) (d'' : nat) (d''' : nat) : (term20 n d'' d''') = (term21 n d'' d''').
Proof. exact (@lem1249998 d'' n (term9 d'' d''')). Qed.
Lemma lem1250007 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250008 (d'' : nat) (n : nat) (d''' : nat) : (term6 n d'' d''') = (term6 d'' n d''').
Proof. exact (@lem1250007 d'' n (S d''')). Qed.
Lemma lem1250018 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1250019 (d'' : nat) (n : nat) (d''' : nat) : (term21 n d'' d''') = (term22 d'' n d''').
Proof. exact (MK_COMB (@lem1250018 d'') (@lem1250008 d'' n d''')). Qed.
Lemma lem1250026 (d'' : nat) (n : nat) (d''' : nat) : (term20 n d'' d''') = (term22 d'' n d''').
Proof. exact (TRANS (@lem1249999 n d'' d''') (@lem1250019 d'' n d''')). Qed.
Lemma lem1250027 (d'' : nat) (n : nat) (d''' : nat) : (term19 n d''' d'') = (term22 d'' n d''').
Proof. exact (TRANS (@lem1249996 n d'' d''') (@lem1250026 d'' n d''')). Qed.
Lemma lem1250028 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250029 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term14 d' n d''' d'') = (term11 d' d'' n d''').
Proof. exact (MK_COMB (@lem1250028 d') (@lem1250027 d'' n d''')). Qed.
Lemma lem1250036 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term14 n d' d''' d'') = (term11 d' d'' n d''').
Proof. exact (TRANS (@lem1249958 d' n d''' d'') (@lem1250029 d' d'' n d''')). Qed.
Lemma lem1250037 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : ((term2 n d' d'' d''') = (term14 n d' d''' d'')) = ((term11 d' d'' n d''') = (term11 d' d'' n d''')).
Proof. exact (MK_COMB (@lem1249955 d' d'' n d''') (@lem1250036 d' d'' n d''')). Qed.
Lemma lem1250039 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1250040 (x : nat) : (x = x) = True.
Proof. exact (@lem1250039 nat x). Qed.
Lemma lem1250041 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : ((term11 d' d'' n d''') = (term11 d' d'' n d''')) = True.
Proof. exact (@lem1250040 (term11 d' d'' n d''')). Qed.
Lemma lem1250042 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term2 n d' d'' d''') = (term14 n d' d''' d'')) = True.
Proof. exact (TRANS (@lem1250037 d' d'' n d''') (@lem1250041 d' d'' n d''')). Qed.
Lemma lem1250043 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : True = ((term2 n d' d'' d''') = (term14 n d' d''' d'')).
Proof. exact (SYM (@lem1250042 n d' d''' d'')). Qed.
Lemma lem1250044 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term2 n d' d'' d''') = (term14 n d' d''' d'').
Proof. exact (EQ_MP (@lem1250043 n d' d''' d'') (@lem0)). Qed.
Lemma lem1250046 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1250047 (x : nat) : (x = x) = True.
Proof. exact (@lem1250046 nat x). Qed.
Lemma lem1250048 (n : nat) (d' : nat) : ((Nat.add n d') = (Nat.add n d')) = True.
Proof. exact (@lem1250047 (Nat.add n d')). Qed.
Lemma lem1250049 (n : nat) (d' : nat) : True = ((Nat.add n d') = (Nat.add n d')).
Proof. exact (SYM (@lem1250048 n d')). Qed.
Lemma lem1250050 (n : nat) (d' : nat) : (Nat.add n d') = (Nat.add n d').
Proof. exact (EQ_MP (@lem1250049 n d') (@lem0)). Qed.
Lemma lem1250051 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1250052 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term12 n d' d'' d''') = (term23 n d' d''' d'').
Proof. exact (MK_COMB (@lem1250051) (@lem1250044 n d' d''' d'')). Qed.
Lemma lem1250053 (d''' : nat) (d'' : nat) (n : nat) (d' : nat) : ((term2 n d' d'' d''') = (Nat.add n d')) = ((term14 n d' d''' d'') = (Nat.add n d')).
Proof. exact (MK_COMB (@lem1250052 n d' d''' d'') (@lem1250050 n d')). Qed.
Lemma lem1250060 (m : nat) : term24 m.
Proof. exact (@lem79890 m). Qed.
Lemma lem1250061 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1250062 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1250061 m) (@lem1250060 m)). Qed.
Lemma lem1250063 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem1250062 m n). Qed.
Lemma lem1250064 (m : nat) (n : nat) : (term26 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem1250066 (m : nat) : term27 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1250067 (m : nat) : (term27 m) = (term28 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem1250068 (m : nat) : term28 m.
Proof. exact (EQ_MP (@lem1250067 m) (@lem1250066 m)). Qed.
Lemma lem1250069 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem1250068 m n). Qed.
Lemma lem1250070 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem1250071 (m : nat) (n : nat) : term30 m n.
Proof. exact (EQ_MP (@lem1250070 m n) (@lem1250069 m n)). Qed.
Lemma lem1250072 (m : nat) (n : nat) (p : nat) : term31 m n p.
Proof. exact (@lem1250071 m n p). Qed.
Lemma lem1250073 (m : nat) (n : nat) (p : nat) : (term31 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term31 m n p)). Qed.
Lemma lem1250076 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1250073 m n p) (@lem1250072 m n p)). Qed.
Lemma lem1250077 (n : nat) (d''' : nat) (d'' : nat) (d' : nat) : ((term14 n d' d''' d'') = (Nat.add n d')) = ((term19 d' d''' d'') = d').
Proof. exact (@lem1250076 n (term19 d' d''' d'') d'). Qed.
Lemma lem1250079 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1250064 m n) (@lem1250063 m n)). Qed.
Lemma lem1250084 (d' : nat) (d''' : nat) (d'' : nat) : ((term19 d' d''' d'') = d') = ((term15 d''' d'') = (NUMERAL 0)).
Proof. exact (@lem1250079 d' (term15 d''' d'')). Qed.
Lemma lem1250085 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term14 n d' d''' d'') = (Nat.add n d')) = ((term15 d''' d'') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1250077 n d''' d'' d') (@lem1250084 d' d''' d'')). Qed.
Lemma lem1250086 (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : (term32 d'' d''' n d') = (term32 d'' d''' n d').
Proof. exact (eq_refl (term32 d'' d''' n d')). Qed.
Lemma lem1250087 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (((term2 n d' d'' d''') = (Nat.add n d')) = ((term14 n d' d''' d'') = (Nat.add n d'))) = (((term2 n d' d'' d''') = (Nat.add n d')) = ((term15 d''' d'') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1250086 d'' d''' n d') (@lem1250085 n d' d''' d'')). Qed.
Lemma lem1250088 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term2 n d' d'' d''') = (Nat.add n d')) = ((term15 d''' d'') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1250087 n d' d''' d'') (@lem1250053 d''' d'' n d')). Qed.
Lemma lem1250089 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1250090 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term33 d'' d''' n d') = (term34 d''' d'').
Proof. exact (MK_COMB (@lem1250089) (@lem1250088 n d' d''' d'')). Qed.
Lemma lem1250091 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1250092 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term35 d'' d''' n d') = (term36 d''' d'').
Proof. exact (MK_COMB (@lem1250090 n d' d''' d'') (@lem1250091)). Qed.
Lemma lem1250093 (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : (term36 d''' d'') = (term35 d'' d''' n d').
Proof. exact (SYM (@lem1250092 n d' d''' d'')). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_SUC_LT_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Require Import thm89994_spec.
Lemma lem90963 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem90964 (m : nat) : term1 m.
Proof. exact (@lem90963 (term2 m)). Qed.
Lemma lem90965 (m : nat) : (term3 m) = ((term4 m) = (term5 m)).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem90966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem90967 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem90966) (@lem90965 m)). Qed.
Lemma lem90968 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem90969 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem90970 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem90969) (@lem90968 m n)). Qed.
Lemma lem90971 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (term14 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem90972 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (MK_COMB (@lem90970 m n) (@lem90971 m n)). Qed.
Lemma lem90973 (m : nat) : (term17 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem90972 m n)). Qed.
Lemma lem90974 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem90975 (m : nat) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem90974) (@lem90973 m)). Qed.
Lemma lem90976 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem90967 m) (@lem90975 m)). Qed.
Lemma lem90977 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem90978 (m : nat) : (term23 m) = (term24 m).
Proof. exact (MK_COMB (@lem90977) (@lem90976 m)). Qed.
Lemma lem90979 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem90980 (m : nat) : (term25 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem90979 m n)). Qed.
Lemma lem90981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem90982 (m : nat) : (term26 m) = (term27 m).
Proof. exact (MK_COMB (@lem90981) (@lem90980 m)). Qed.
Lemma lem90983 (m : nat) : (term1 m) = (term28 m).
Proof. exact (MK_COMB (@lem90978 m) (@lem90982 m)). Qed.
Lemma lem90984 (m : nat) : term28 m.
Proof. exact (EQ_MP (@lem90983 m) (@lem90964 m)). Qed.
Lemma lem90992 (n : nat) : term29 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem90993 (n : nat) : (term29 n) = (term30 n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem90994 (n : nat) : term30 n.
Proof. exact (EQ_MP (@lem90993 n) (@lem90992 n)). Qed.
Lemma lem90995 (n : nat) : term31 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem91015 : term32.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem91016 (m : nat) : term33 m.
Proof. exact (@lem91015 m). Qed.
Lemma lem91017 (m : nat) : (term33 m) = ((term5 m) = False).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem91026 : term34.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem91027 (m : nat) : term35 m.
Proof. exact (@lem91026 m). Qed.
Lemma lem91028 (m : nat) : (term35 m) = ((term36 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem91033 (m : nat) : (term36 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem91028 m) (@lem91027 m)). Qed.
Lemma lem91034 (m : nat) : (term4 m) = ((S m) = (NUMERAL 0)).
Proof. exact (@lem91033 (S m)). Qed.
Lemma lem91036 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem90995 n (@lem90994 n)). Qed.
Lemma lem91037 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem91036 m). Qed.
Lemma lem91038 (m : nat) : (term4 m) = False.
Proof. exact (TRANS (@lem91034 m) (@lem91037 m)). Qed.
Lemma lem91039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem91040 (m : nat) : (term37 m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem91039) (@lem91038 m)). Qed.
Lemma lem91042 (m : nat) : (term5 m) = False.
Proof. exact (EQ_MP (@lem91017 m) (@lem91016 m)). Qed.
Lemma lem91043 (m : nat) : ((term4 m) = (term5 m)) = (False = False).
Proof. exact (MK_COMB (@lem91040 m) (@lem91042 m)). Qed.
Lemma lem91045 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem91046 : (False = False) = (~ False).
Proof. exact (@lem91045 False). Qed.
Lemma lem91048 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem91049 : (False = False) = True.
Proof. exact (TRANS (@lem91046) (@lem91048)). Qed.
Lemma lem91050 (m : nat) : ((term4 m) = (term5 m)) = True.
Proof. exact (TRANS (@lem91043 m) (@lem91049)). Qed.
Lemma lem91051 (m : nat) : True = ((term4 m) = (term5 m)).
Proof. exact (SYM (@lem91050 m)). Qed.
Lemma lem91052 (m : nat) : (term4 m) = (term5 m).
Proof. exact (EQ_MP (@lem91051 m) (@lem0)). Qed.
Lemma lem91053 (m : nat) : term38 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem91054 (m : nat) : (term38 m) = (term39 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem91055 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem91054 m) (@lem91053 m)). Qed.
Lemma lem91056 (m : nat) (n : nat) : term40 m n.
Proof. exact (@lem91055 m n). Qed.
Lemma lem91057 (m : nat) (n : nat) : (term40 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem91075 : term41.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem91076 (m : nat) : term42 m.
Proof. exact (@lem91075 m). Qed.
Lemma lem91077 (m : nat) : (term42 m) = (term43 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem91078 (m : nat) : term43 m.
Proof. exact (EQ_MP (@lem91077 m) (@lem91076 m)). Qed.
Lemma lem91079 (m : nat) (n : nat) : term44 m n.
Proof. exact (@lem91078 m n). Qed.
Lemma lem91080 (m : nat) (n : nat) : (term44 m n) = ((term14 m n) = (term45 m n)).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem91086 : term46.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem91087 (m : nat) : term47 m.
Proof. exact (@lem91086 m). Qed.
Lemma lem91088 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem91089 (m : nat) : term48 m.
Proof. exact (EQ_MP (@lem91088 m) (@lem91087 m)). Qed.
Lemma lem91090 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem91089 m n). Qed.
Lemma lem91091 (m : nat) (n : nat) : (term49 m n) = ((term50 m n) = (term51 m n)).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem91100 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (EQ_MP (@lem91091 m n) (@lem91090 m n)). Qed.
Lemma lem91101 (m : nat) (n : nat) : (term13 m n) = (term52 m n).
Proof. exact (@lem91100 (S m) n). Qed.
Lemma lem91105 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem91057 m n) (@lem91056 m n)). Qed.
Lemma lem91108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem91109 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (MK_COMB (@lem91108) (@lem91105 m n)). Qed.
Lemma lem91111 (m : nat) (n : nat) (h1 : (term9 m n) = (Peano.lt m n)) : (term9 m n) = (Peano.lt m n).
Proof. exact (h1). Qed.
Lemma lem91112 (m : nat) (n : nat) (h1 : (term9 m n) = (Peano.lt m n)) : (term52 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem91109 m n) (@lem91111 m n h1)). Qed.
Lemma lem91115 (m : nat) (n : nat) (h1 : (term9 m n) = (Peano.lt m n)) : (term13 m n) = (term45 m n).
Proof. exact (TRANS (@lem91101 m n) (@lem91112 m n h1)). Qed.
Lemma lem91116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem91117 (m : nat) (n : nat) (h1 : (term9 m n) = (Peano.lt m n)) : (term55 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem91116) (@lem91115 m n h1)). Qed.
Lemma lem91119 (m : nat) (n : nat) : (term14 m n) = (term45 m n).
Proof. exact (EQ_MP (@lem91080 m n) (@lem91079 m n)). Qed.
Lemma lem91124 (m : nat) (n : nat) (h1 : (term9 m n) = (Peano.lt m n)) : ((term13 m n) = (term14 m n)) = ((term45 m n) = (term45 m n)).
Proof. exact (MK_COMB (@lem91117 m n h1) (@lem91119 m n)). Qed.
Lemma lem91126 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem91127 (x : Prop) : (x = x) = True.
Proof. exact (@lem91126 Prop x). Qed.
Lemma lem91128 (m : nat) (n : nat) : ((term45 m n) = (term45 m n)) = True.
Proof. exact (@lem91127 (term45 m n)). Qed.
Lemma lem91129 (m : nat) (n : nat) (h1 : (term9 m n) = (Peano.lt m n)) : ((term13 m n) = (term14 m n)) = True.
Proof. exact (TRANS (@lem91124 m n h1) (@lem91128 m n)). Qed.
Lemma lem91130 (m : nat) (n : nat) (h1 : (term9 m n) = (Peano.lt m n)) : True = ((term13 m n) = (term14 m n)).
Proof. exact (SYM (@lem91129 m n h1)). Qed.
Lemma lem91131 (m : nat) (n : nat) (h1 : (term9 m n) = (Peano.lt m n)) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem91130 m n h1) (@lem0)). Qed.
Lemma lem91132 (m : nat) (n : nat) : term16 m n.
Proof. exact (fun h0 : (term9 m n) = (Peano.lt m n) => @lem91131 m n h0). Qed.
Lemma lem91137 (m : nat) : term20 m.
Proof. exact (fun n : nat => @lem91132 m n). Qed.
Lemma lem91138 (m : nat) : term22 m.
Proof. exact (conj (@lem91052 m) (@lem91137 m)). Qed.
Lemma lem91139 (m : nat) : term27 m.
Proof. exact (@lem90984 m (@lem91138 m)). Qed.
Lemma lem91144 : term57.
Proof. exact (fun m : nat => @lem91139 m). Qed.

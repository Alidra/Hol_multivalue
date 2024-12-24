Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PCROSS_SING_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_SING_spec.
Require Import PASTECART_INJ_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8005966 {A M N : Type'} (x : cart A M) : term0 A M N x.
Proof. exact (@lem7664494 A M N x). Qed.
Lemma lem8005967 {A M N : Type'} (x : cart A M) : (term0 A M N x) = (term1 A M N x).
Proof. exact (eq_refl (term0 A M N x)). Qed.
Lemma lem8005968 {A M N : Type'} (x : cart A M) : term1 A M N x.
Proof. exact (EQ_MP (@lem8005967 A M N x) (@lem8005966 A M N x)). Qed.
Lemma lem8005969 {A M N : Type'} (x : cart A M) (y : cart A N) : term2 A M N x y.
Proof. exact (@lem8005968 A M N x y). Qed.
Lemma lem8005970 {A M N : Type'} (x : cart A M) (y : cart A N) : (term2 A M N x y) = (term3 A M N x y).
Proof. exact (eq_refl (term2 A M N x y)). Qed.
Lemma lem8005971 {A M N : Type'} (x : cart A M) (y : cart A N) : term3 A M N x y.
Proof. exact (EQ_MP (@lem8005970 A M N x y) (@lem8005969 A M N x y)). Qed.
Lemma lem8005972 {A M N : Type'} (x : cart A M) (y : cart A N) (w : cart A M) : term4 A M N x y w.
Proof. exact (@lem8005971 A M N x y w). Qed.
Lemma lem8005973 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) : (term4 A M N x y w) = (term5 A M N x w y).
Proof. exact (eq_refl (term4 A M N x y w)). Qed.
Lemma lem8005974 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) : term5 A M N x w y.
Proof. exact (EQ_MP (@lem8005973 A M N x w y) (@lem8005972 A M N x y w)). Qed.
Lemma lem8005975 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) (z : cart A N) : term6 A M N x w y z.
Proof. exact (@lem8005974 A M N x w y z). Qed.
Lemma lem8005976 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) (z : cart A N) : (term6 A M N x w y z) = (((@pastecart A M N x y) = (@pastecart A M N w z)) = (term7 A M N x w y z)).
Proof. exact (eq_refl (term6 A M N x w y z)). Qed.
Lemma lem8005978 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term8 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8005979 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term8 _141927 _141928 _141929 s) = (term9 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term8 _141927 _141928 _141929 s)). Qed.
Lemma lem8005980 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term9 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8005979 _141927 _141928 _141929 s) (@lem8005978 _141927 _141928 _141929 s)). Qed.
Lemma lem8005981 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term10 _141927 _141928 _141929 s t.
Proof. exact (@lem8005980 _141927 _141928 _141929 s t). Qed.
Lemma lem8005982 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term10 _141927 _141928 _141929 s t) = (term11 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term10 _141927 _141928 _141929 s t)). Qed.
Lemma lem8005983 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term11 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8005982 _141927 _141928 _141929 s t) (@lem8005981 _141927 _141928 _141929 s t)). Qed.
Lemma lem8005984 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term12 _141927 _141928 _141929 s t x.
Proof. exact (@lem8005983 _141927 _141928 _141929 s t x). Qed.
Lemma lem8005985 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term12 _141927 _141928 _141929 s t x) = (term13 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term12 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8005986 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term13 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8005985 _141927 _141928 _141929 x s t) (@lem8005984 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8005987 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term14 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8005986 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8005988 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term14 _141927 _141928 _141929 x s t y) = ((term15 _141927 _141928 _141929 x y s t) = (term16 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term14 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8005990 {A : Type'} (x : A) : term17 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem8005991 {A : Type'} (x : A) : (term17 A x) = (term18 A x).
Proof. exact (eq_refl (term17 A x)). Qed.
Lemma lem8005992 {A : Type'} (x : A) : term18 A x.
Proof. exact (EQ_MP (@lem8005991 A x) (@lem8005990 A x)). Qed.
Lemma lem8005993 {A : Type'} (x : A) (y : A) : term19 A x y.
Proof. exact (@lem8005992 A x y). Qed.
Lemma lem8005994 {A : Type'} (x : A) (y : A) : (term19 A x y) = ((term20 A x y) = (x = y)).
Proof. exact (eq_refl (term19 A x y)). Qed.
Lemma lem8005996 {A : Type'} (s : A -> Prop) : term21 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8005997 {A : Type'} (s : A -> Prop) : (term21 A s) = (term22 A s).
Proof. exact (eq_refl (term21 A s)). Qed.
Lemma lem8005998 {A : Type'} (s : A -> Prop) : term22 A s.
Proof. exact (EQ_MP (@lem8005997 A s) (@lem8005996 A s)). Qed.
Lemma lem8005999 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term23 A s t.
Proof. exact (@lem8005998 A s t). Qed.
Lemma lem8006000 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = ((s = t) = (term24 A s t)).
Proof. exact (eq_refl (term23 A s t)). Qed.
Lemma lem8006017 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (EQ_MP (@lem8006000 A s t) (@lem8005999 A s t)). Qed.
Lemma lem8006018 {_142030 A N : Type'} (s : type25 _142030 A N) (t : type25 _142030 A N) : (s = t) = (term25 _142030 A N s t).
Proof. exact (@lem8006017 (type3 _142030 A N) s t). Qed.
Lemma lem8006019 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : ((term26 _142030 A N x y) = (term27 _142030 A N x y)) = (term28 _142030 A N x y).
Proof. exact (@lem8006018 _142030 A N (term26 _142030 A N x y) (term27 _142030 A N x y)). Qed.
Lemma lem8006025 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term29 _140454 _140455 _140456 P) = (term30 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8006026 {_142030 A N : Type'} (P : type25 _142030 A N) : (term31 _142030 A N P) = (term32 _142030 A N P).
Proof. exact (@lem8006025 A _142030 N P). Qed.
Lemma lem8006027 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : (term33 _142030 A N x y) = (term34 _142030 A N x y).
Proof. exact (@lem8006026 _142030 A N (term35 _142030 A N x y)). Qed.
Lemma lem8006028 {_142030 A N : Type'} (x : type3 _142030 A N) (x' : cart A _142030) (y : cart A N) : (term36 _142030 A N x' y x) = ((term37 _142030 A N x x' y) = (term38 _142030 A N x x' y)).
Proof. exact (eq_refl (term36 _142030 A N x' y x)). Qed.
Lemma lem8006029 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : (term39 _142030 A N x y) = (term35 _142030 A N x y).
Proof. exact (fun_ext (fun x' : type3 _142030 A N => @lem8006028 _142030 A N x' x y)). Qed.
Lemma lem8006030 {_142030 A N : Type'} : (@all (cart A (finite_sum _142030 N))) = (@all (cart A (finite_sum _142030 N))).
Proof. exact (eq_refl (@all (cart A (finite_sum _142030 N)))). Qed.
Lemma lem8006031 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : (term33 _142030 A N x y) = (term28 _142030 A N x y).
Proof. exact (MK_COMB (@lem8006030 _142030 A N) (@lem8006029 _142030 A N x y)). Qed.
Lemma lem8006032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8006033 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : (term40 _142030 A N x y) = (term41 _142030 A N x y).
Proof. exact (MK_COMB (@lem8006032) (@lem8006031 _142030 A N x y)). Qed.
Lemma lem8006034 {_142030 A N : Type'} (x' : cart A _142030) (y' : cart A N) (x : cart A _142030) (y : cart A N) : (term42 _142030 A N x y x' y') = ((term43 _142030 A N x' y' x y) = (term44 _142030 A N x' y' x y)).
Proof. exact (eq_refl (term42 _142030 A N x y x' y')). Qed.
Lemma lem8006035 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y : cart A N) : (term45 _142030 A N x y x') = (term46 _142030 A N x' x y).
Proof. exact (fun_ext (fun y' : cart A N => @lem8006034 _142030 A N x' y' x y)). Qed.
Lemma lem8006036 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8006037 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y : cart A N) : (term47 _142030 A N x y x') = (term48 _142030 A N x' x y).
Proof. exact (MK_COMB (@lem8006036 A N) (@lem8006035 _142030 A N x' x y)). Qed.
Lemma lem8006038 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : (term49 _142030 A N x y) = (term50 _142030 A N x y).
Proof. exact (fun_ext (fun x' : cart A _142030 => @lem8006037 _142030 A N x' x y)). Qed.
Lemma lem8006039 {_142030 A : Type'} : (@all (cart A _142030)) = (@all (cart A _142030)).
Proof. exact (eq_refl (@all (cart A _142030))). Qed.
Lemma lem8006040 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : (term34 _142030 A N x y) = (term51 _142030 A N x y).
Proof. exact (MK_COMB (@lem8006039 _142030 A) (@lem8006038 _142030 A N x y)). Qed.
Lemma lem8006041 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : ((term33 _142030 A N x y) = (term34 _142030 A N x y)) = ((term28 _142030 A N x y) = (term51 _142030 A N x y)).
Proof. exact (MK_COMB (@lem8006033 _142030 A N x y) (@lem8006040 _142030 A N x y)). Qed.
Lemma lem8006042 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : (term28 _142030 A N x y) = (term51 _142030 A N x y).
Proof. exact (EQ_MP (@lem8006041 _142030 A N x y) (@lem8006027 _142030 A N x y)). Qed.
Lemma lem8006049 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : ((term26 _142030 A N x y) = (term27 _142030 A N x y)) = (term51 _142030 A N x y).
Proof. exact (TRANS (@lem8006019 _142030 A N x y) (@lem8006042 _142030 A N x y)). Qed.
Lemma lem8006061 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term15 _141927 _141928 _141929 x y s t) = (term16 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8005988 _141927 _141928 _141929 x s y t) (@lem8005987 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8006062 {_142030 A N : Type'} (x : cart A _142030) (s : type26 _142030 A) (y : cart A N) (t : type24 A N) : (term52 _142030 A N x y s t) = (term53 _142030 A N x s y t).
Proof. exact (@lem8006061 A _142030 N x s y t). Qed.
Lemma lem8006063 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y' : cart A N) (y : cart A N) : (term43 _142030 A N x' y' x y) = (term54 _142030 A N x' x y' y).
Proof. exact (@lem8006062 _142030 A N x' (@INSERT (cart A _142030) x (@EMPTY (cart A _142030))) y' (@INSERT (cart A N) y (@EMPTY (cart A N)))). Qed.
Lemma lem8006067 {A : Type'} (x : A) (y : A) : (term20 A x y) = (x = y).
Proof. exact (EQ_MP (@lem8005994 A x y) (@lem8005993 A x y)). Qed.
Lemma lem8006068 {_142030 A : Type'} (x : cart A _142030) (y : cart A _142030) : (term55 _142030 A x y) = (x = y).
Proof. exact (@lem8006067 (cart A _142030) x y). Qed.
Lemma lem8006069 {_142030 A : Type'} (x' : cart A _142030) (x : cart A _142030) : (term55 _142030 A x' x) = (x' = x).
Proof. exact (@lem8006068 _142030 A x' x). Qed.
Lemma lem8006074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8006075 {_142030 A : Type'} (x' : cart A _142030) (x : cart A _142030) : (term56 _142030 A x' x) = (term57 _142030 A x' x).
Proof. exact (MK_COMB (@lem8006074) (@lem8006069 _142030 A x' x)). Qed.
Lemma lem8006077 {A : Type'} (x : A) (y : A) : (term20 A x y) = (x = y).
Proof. exact (EQ_MP (@lem8005994 A x y) (@lem8005993 A x y)). Qed.
Lemma lem8006078 {A N : Type'} (x : cart A N) (y : cart A N) : (term58 A N x y) = (x = y).
Proof. exact (@lem8006077 (cart A N) x y). Qed.
Lemma lem8006079 {A N : Type'} (y' : cart A N) (y : cart A N) : (term58 A N y' y) = (y' = y).
Proof. exact (@lem8006078 A N y' y). Qed.
Lemma lem8006084 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y' : cart A N) (y : cart A N) : (term54 _142030 A N x' x y' y) = (term59 _142030 A N x' x y' y).
Proof. exact (MK_COMB (@lem8006075 _142030 A x' x) (@lem8006079 A N y' y)). Qed.
Lemma lem8006087 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y' : cart A N) (y : cart A N) : (term43 _142030 A N x' y' x y) = (term59 _142030 A N x' x y' y).
Proof. exact (TRANS (@lem8006063 _142030 A N x' x y' y) (@lem8006084 _142030 A N x' x y' y)). Qed.
Lemma lem8006088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8006089 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y' : cart A N) (y : cart A N) : (term60 _142030 A N x' y' x y) = (term61 _142030 A N x' x y' y).
Proof. exact (MK_COMB (@lem8006088) (@lem8006087 _142030 A N x' x y' y)). Qed.
Lemma lem8006091 {A : Type'} (x : A) (y : A) : (term20 A x y) = (x = y).
Proof. exact (EQ_MP (@lem8005994 A x y) (@lem8005993 A x y)). Qed.
Lemma lem8006092 {_142030 A N : Type'} (x : type3 _142030 A N) (y : type3 _142030 A N) : (term62 _142030 A N x y) = (x = y).
Proof. exact (@lem8006091 (type3 _142030 A N) x y). Qed.
Lemma lem8006093 {_142030 A N : Type'} (x' : cart A _142030) (y' : cart A N) (x : cart A _142030) (y : cart A N) : (term44 _142030 A N x' y' x y) = ((@pastecart A _142030 N x' y') = (@pastecart A _142030 N x y)).
Proof. exact (@lem8006092 _142030 A N (@pastecart A _142030 N x' y') (@pastecart A _142030 N x y)). Qed.
Lemma lem8006095 {A M N : Type'} (x : cart A M) (w : cart A M) (y : cart A N) (z : cart A N) : ((@pastecart A M N x y) = (@pastecart A M N w z)) = (term7 A M N x w y z).
Proof. exact (EQ_MP (@lem8005976 A M N x w y z) (@lem8005975 A M N x w y z)). Qed.
Lemma lem8006096 {_142030 A N : Type'} (x : cart A _142030) (w : cart A _142030) (y : cart A N) (z : cart A N) : ((@pastecart A _142030 N x y) = (@pastecart A _142030 N w z)) = (term59 _142030 A N x w y z).
Proof. exact (@lem8006095 A _142030 N x w y z). Qed.
Lemma lem8006097 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y' : cart A N) (y : cart A N) : ((@pastecart A _142030 N x' y') = (@pastecart A _142030 N x y)) = (term59 _142030 A N x' x y' y).
Proof. exact (@lem8006096 _142030 A N x' x y' y). Qed.
Lemma lem8006100 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y' : cart A N) (y : cart A N) : (term44 _142030 A N x' y' x y) = (term59 _142030 A N x' x y' y).
Proof. exact (TRANS (@lem8006093 _142030 A N x' y' x y) (@lem8006097 _142030 A N x' x y' y)). Qed.
Lemma lem8006109 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y' : cart A N) (y : cart A N) : ((term43 _142030 A N x' y' x y) = (term44 _142030 A N x' y' x y)) = ((term59 _142030 A N x' x y' y) = (term59 _142030 A N x' x y' y)).
Proof. exact (MK_COMB (@lem8006089 _142030 A N x' x y' y) (@lem8006100 _142030 A N x' x y' y)). Qed.
Lemma lem8006111 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8006112 (x : Prop) : (x = x) = True.
Proof. exact (@lem8006111 Prop x). Qed.
Lemma lem8006113 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y' : cart A N) (y : cart A N) : ((term59 _142030 A N x' x y' y) = (term59 _142030 A N x' x y' y)) = True.
Proof. exact (@lem8006112 (term59 _142030 A N x' x y' y)). Qed.
Lemma lem8006114 {_142030 A N : Type'} (x' : cart A _142030) (y' : cart A N) (x : cart A _142030) (y : cart A N) : ((term43 _142030 A N x' y' x y) = (term44 _142030 A N x' y' x y)) = True.
Proof. exact (TRANS (@lem8006109 _142030 A N x' x y' y) (@lem8006113 _142030 A N x' x y' y)). Qed.
Lemma lem8006115 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y : cart A N) : (term46 _142030 A N x' x y) = (term63 A N).
Proof. exact (fun_ext (fun y' : cart A N => @lem8006114 _142030 A N x' y' x y)). Qed.
Lemma lem8006116 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8006117 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y : cart A N) : (term48 _142030 A N x' x y) = (term64 A N).
Proof. exact (MK_COMB (@lem8006116 A N) (@lem8006115 _142030 A N x' x y)). Qed.
Lemma lem8006119 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8006120 {A N : Type'} (t : Prop) : (term66 A N t) = t.
Proof. exact (@lem8006119 (cart A N) t). Qed.
Lemma lem8006121 {A N : Type'} : (term64 A N) = True.
Proof. exact (@lem8006120 A N True). Qed.
Lemma lem8006122 {_142030 A N : Type'} (x' : cart A _142030) (x : cart A _142030) (y : cart A N) : (term48 _142030 A N x' x y) = True.
Proof. exact (TRANS (@lem8006117 _142030 A N x' x y) (@lem8006121 A N)). Qed.
Lemma lem8006123 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : (term50 _142030 A N x y) = (term67 _142030 A).
Proof. exact (fun_ext (fun x' : cart A _142030 => @lem8006122 _142030 A N x' x y)). Qed.
Lemma lem8006124 {_142030 A : Type'} : (@all (cart A _142030)) = (@all (cart A _142030)).
Proof. exact (eq_refl (@all (cart A _142030))). Qed.
Lemma lem8006125 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : (term51 _142030 A N x y) = (term68 _142030 A).
Proof. exact (MK_COMB (@lem8006124 _142030 A) (@lem8006123 _142030 A N x y)). Qed.
Lemma lem8006127 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8006128 {_142030 A : Type'} (t : Prop) : (term69 _142030 A t) = t.
Proof. exact (@lem8006127 (cart A _142030) t). Qed.
Lemma lem8006129 {_142030 A : Type'} : (term68 _142030 A) = True.
Proof. exact (@lem8006128 _142030 A True). Qed.
Lemma lem8006130 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : (term51 _142030 A N x y) = True.
Proof. exact (TRANS (@lem8006125 _142030 A N x y) (@lem8006129 _142030 A)). Qed.
Lemma lem8006131 {_142030 A N : Type'} (x : cart A _142030) (y : cart A N) : ((term26 _142030 A N x y) = (term27 _142030 A N x y)) = True.
Proof. exact (TRANS (@lem8006049 _142030 A N x y) (@lem8006130 _142030 A N x y)). Qed.
Lemma lem8006132 {_142030 A N : Type'} (x : cart A _142030) : (term70 _142030 A N x) = (term63 A N).
Proof. exact (fun_ext (fun y : cart A N => @lem8006131 _142030 A N x y)). Qed.
Lemma lem8006133 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8006134 {_142030 A N : Type'} (x : cart A _142030) : (term71 _142030 A N x) = (term64 A N).
Proof. exact (MK_COMB (@lem8006133 A N) (@lem8006132 _142030 A N x)). Qed.
Lemma lem8006136 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8006137 {A N : Type'} (t : Prop) : (term66 A N t) = t.
Proof. exact (@lem8006136 (cart A N) t). Qed.
Lemma lem8006138 {A N : Type'} : (term64 A N) = True.
Proof. exact (@lem8006137 A N True). Qed.
Lemma lem8006139 {_142030 A N : Type'} (x : cart A _142030) : (term71 _142030 A N x) = True.
Proof. exact (TRANS (@lem8006134 _142030 A N x) (@lem8006138 A N)). Qed.
Lemma lem8006140 {_142030 A N : Type'} : (term72 _142030 A N) = (term67 _142030 A).
Proof. exact (fun_ext (fun x : cart A _142030 => @lem8006139 _142030 A N x)). Qed.
Lemma lem8006141 {_142030 A : Type'} : (@all (cart A _142030)) = (@all (cart A _142030)).
Proof. exact (eq_refl (@all (cart A _142030))). Qed.
Lemma lem8006142 {_142030 A N : Type'} : (term73 _142030 A N) = (term68 _142030 A).
Proof. exact (MK_COMB (@lem8006141 _142030 A) (@lem8006140 _142030 A N)). Qed.
Lemma lem8006144 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8006145 {_142030 A : Type'} (t : Prop) : (term69 _142030 A t) = t.
Proof. exact (@lem8006144 (cart A _142030) t). Qed.
Lemma lem8006146 {_142030 A : Type'} : (term68 _142030 A) = True.
Proof. exact (@lem8006145 _142030 A True). Qed.
Lemma lem8006147 {_142030 A N : Type'} : (term73 _142030 A N) = True.
Proof. exact (TRANS (@lem8006142 _142030 A N) (@lem8006146 _142030 A)). Qed.
Lemma lem8006148 {_142030 A N : Type'} : True = (term73 _142030 A N).
Proof. exact (SYM (@lem8006147 _142030 A N)). Qed.
Lemma lem8006149 {_142030 A N : Type'} : term73 _142030 A N.
Proof. exact (EQ_MP (@lem8006148 _142030 A N) (@lem0)). Qed.

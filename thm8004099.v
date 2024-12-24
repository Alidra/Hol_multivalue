Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8004099_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import EXISTS_IN_GSPEC_spec.
Require Import PCROSS_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem8003922 (t1 : Prop) : term0 t1.
Proof. exact (@lem512 t1). Qed.
Lemma lem8003923 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8003924 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8003923 t1) (@lem8003922 t1)). Qed.
Lemma lem8003925 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8003924 t1 t2). Qed.
Lemma lem8003926 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8003927 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8003926 t1 t2) (@lem8003925 t1 t2)). Qed.
Lemma lem8003928 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8003927 t1 t2 t3). Qed.
Lemma lem8003929 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8003931 {_89212 _89213 _89280 _89281 _89282 _89357 _89358 _89359 _89360 _89361 : Type'} (Q : _89357 -> Prop) : term7 _89212 _89213 _89280 _89281 _89282 _89357 _89358 _89359 _89360 _89361 Q.
Proof. exact (proj2 (@lem3449335 Prop _89212 _89213 _89280 _89281 _89282 _89357 _89358 _89359 _89360 _89361 Q)). Qed.
Lemma lem8003947 {_89212 _89213 _89357 : Type'} (Q : _89357 -> Prop) : term8 _89212 _89213 _89357 Q.
Proof. exact (proj1 (@lem8003931 _89212 _89213 Prop Prop Prop _89357 Prop Prop Prop Prop Q)). Qed.
Lemma lem8003948 {_89212 _89213 _89357 : Type'} (Q : _89357 -> Prop) (P : type1470 _89212 _89213) : term9 _89212 _89213 _89357 Q P.
Proof. exact (@lem8003947 _89212 _89213 _89357 Q P). Qed.
Lemma lem8003949 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) : (term9 _89212 _89213 _89357 Q P) = (term10 _89212 _89213 _89357 P Q).
Proof. exact (eq_refl (term9 _89212 _89213 _89357 Q P)). Qed.
Lemma lem8003950 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) : term10 _89212 _89213 _89357 P Q.
Proof. exact (EQ_MP (@lem8003949 _89212 _89213 _89357 P Q) (@lem8003948 _89212 _89213 _89357 Q P)). Qed.
Lemma lem8003951 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) (f : type1469 _89212 _89213 _89357) : term11 _89212 _89213 _89357 P Q f.
Proof. exact (@lem8003950 _89212 _89213 _89357 P Q f). Qed.
Lemma lem8003952 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) (f : type1469 _89212 _89213 _89357) : (term11 _89212 _89213 _89357 P Q f) = ((term12 _89212 _89213 _89357 P f Q) = (term13 _89212 _89213 _89357 P Q f)).
Proof. exact (eq_refl (term11 _89212 _89213 _89357 P Q f)). Qed.
Lemma lem8003961 {A M N : Type'} (s : type24 A M) : term14 A M N s.
Proof. exact (@lem8003767 A M N s). Qed.
Lemma lem8003962 {A M N : Type'} (s : type24 A M) : (term14 A M N s) = (term15 A M N s).
Proof. exact (eq_refl (term14 A M N s)). Qed.
Lemma lem8003963 {A M N : Type'} (s : type24 A M) : term15 A M N s.
Proof. exact (EQ_MP (@lem8003962 A M N s) (@lem8003961 A M N s)). Qed.
Lemma lem8003964 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term16 A M N s t.
Proof. exact (@lem8003963 A M N s t). Qed.
Lemma lem8003965 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term16 A M N s t) = ((@PCROSS A M N s t) = (term17 A M N s t)).
Proof. exact (eq_refl (term16 A M N s t)). Qed.
Lemma lem8003976 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (@PCROSS A M N s t) = (term17 A M N s t).
Proof. exact (EQ_MP (@lem8003965 A M N s t) (@lem8003964 A M N s t)). Qed.
Lemma lem8003977 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) : (@PCROSS _141895 _141896 _141897 s t) = (term17 _141895 _141896 _141897 s t).
Proof. exact (@lem8003976 _141895 _141896 _141897 s t). Qed.
Lemma lem8003988 {_141895 _141896 _141897 : Type'} (z : type2 _141895 _141896 _141897) : (@IN (cart _141895 (finite_sum _141896 _141897)) z) = (@IN (cart _141895 (finite_sum _141896 _141897)) z).
Proof. exact (eq_refl (@IN (cart _141895 (finite_sum _141896 _141897)) z)). Qed.
Lemma lem8003989 {_141895 _141896 _141897 : Type'} (z : type2 _141895 _141896 _141897) (s : type24 _141895 _141896) (t : type24 _141895 _141897) : (term18 _141895 _141896 _141897 z s t) = (term19 _141895 _141896 _141897 z s t).
Proof. exact (MK_COMB (@lem8003988 _141895 _141896 _141897 z) (@lem8003977 _141895 _141896 _141897 s t)). Qed.
Lemma lem8003990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8003991 {_141895 _141896 _141897 : Type'} (z : type2 _141895 _141896 _141897) (s : type24 _141895 _141896) (t : type24 _141895 _141897) : (term20 _141895 _141896 _141897 z s t) = (term21 _141895 _141896 _141897 z s t).
Proof. exact (MK_COMB (@lem8003990) (@lem8003989 _141895 _141896 _141897 z s t)). Qed.
Lemma lem8003992 {_141895 _141896 _141897 : Type'} (P : type16 _141895 _141896 _141897) (z : type2 _141895 _141896 _141897) : (P z) = (P z).
Proof. exact (eq_refl (P z)). Qed.
Lemma lem8003993 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) (z : type2 _141895 _141896 _141897) : (term22 _141895 _141896 _141897 s t P z) = (term23 _141895 _141896 _141897 s t P z).
Proof. exact (MK_COMB (@lem8003991 _141895 _141896 _141897 z s t) (@lem8003992 _141895 _141896 _141897 P z)). Qed.
Lemma lem8003996 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term24 _141895 _141896 _141897 s t P) = (term25 _141895 _141896 _141897 s t P).
Proof. exact (fun_ext (fun z : type2 _141895 _141896 _141897 => @lem8003993 _141895 _141896 _141897 s t P z)). Qed.
Lemma lem8003997 {_141895 _141896 _141897 : Type'} : (@ex (cart _141895 (finite_sum _141896 _141897))) = (@ex (cart _141895 (finite_sum _141896 _141897))).
Proof. exact (eq_refl (@ex (cart _141895 (finite_sum _141896 _141897)))). Qed.
Lemma lem8003998 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term26 _141895 _141896 _141897 s t P) = (term27 _141895 _141896 _141897 s t P).
Proof. exact (MK_COMB (@lem8003997 _141895 _141896 _141897) (@lem8003996 _141895 _141896 _141897 s t P)). Qed.
Lemma lem8004000 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) (f : type1469 _89212 _89213 _89357) : (term12 _89212 _89213 _89357 P f Q) = (term13 _89212 _89213 _89357 P Q f).
Proof. exact (EQ_MP (@lem8003952 _89212 _89213 _89357 P Q f) (@lem8003951 _89212 _89213 _89357 P Q f)). Qed.
Lemma lem8004001 {_141895 _141896 _141897 : Type'} (P : type22 _141895 _141896 _141897) (Q : type16 _141895 _141896 _141897) (f : type20 _141895 _141896 _141897) : (term28 _141895 _141896 _141897 P f Q) = (term29 _141895 _141896 _141897 P Q f).
Proof. exact (@lem8004000 (cart _141895 _141897) (cart _141895 _141896) (type2 _141895 _141896 _141897) P Q f). Qed.
Lemma lem8004002 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term30 _141895 _141896 _141897 s t P) = (term31 _141895 _141896 _141897 s t P).
Proof. exact (@lem8004001 _141895 _141896 _141897 (term32 _141895 _141896 _141897 s t) P (@pastecart _141895 _141896 _141897)). Qed.
Lemma lem8004003 {_141895 _141896 _141897 : Type'} (x : cart _141895 _141896) (s : type24 _141895 _141896) (t : type24 _141895 _141897) : (term33 _141895 _141896 _141897 s t x) = (term34 _141895 _141896 _141897 x s t).
Proof. exact (eq_refl (term33 _141895 _141896 _141897 s t x)). Qed.
Lemma lem8004004 {_141895 _141897 : Type'} (y : cart _141895 _141897) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8004005 {_141895 _141896 _141897 : Type'} (x : cart _141895 _141896) (s : type24 _141895 _141896) (t : type24 _141895 _141897) (y : cart _141895 _141897) : (term35 _141895 _141896 _141897 s t x y) = (term36 _141895 _141896 _141897 x s t y).
Proof. exact (MK_COMB (@lem8004003 _141895 _141896 _141897 x s t) (@lem8004004 _141895 _141897 y)). Qed.
Lemma lem8004006 {_141895 _141896 _141897 : Type'} (x : cart _141895 _141896) (s : type24 _141895 _141896) (y : cart _141895 _141897) (t : type24 _141895 _141897) : (term36 _141895 _141896 _141897 x s t y) = (term37 _141895 _141896 _141897 x s y t).
Proof. exact (eq_refl (term36 _141895 _141896 _141897 x s t y)). Qed.
Lemma lem8004007 {_141895 _141896 _141897 : Type'} (x : cart _141895 _141896) (s : type24 _141895 _141896) (y : cart _141895 _141897) (t : type24 _141895 _141897) : (term35 _141895 _141896 _141897 s t x y) = (term37 _141895 _141896 _141897 x s y t).
Proof. exact (TRANS (@lem8004005 _141895 _141896 _141897 x s t y) (@lem8004006 _141895 _141896 _141897 x s y t)). Qed.
Lemma lem8004008 {_141895 _141896 _141897 : Type'} (GEN_PVAR_361 : type2 _141895 _141896 _141897) : (@SETSPEC (cart _141895 (finite_sum _141896 _141897)) GEN_PVAR_361) = (@SETSPEC (cart _141895 (finite_sum _141896 _141897)) GEN_PVAR_361).
Proof. exact (eq_refl (@SETSPEC (cart _141895 (finite_sum _141896 _141897)) GEN_PVAR_361)). Qed.
Lemma lem8004009 {_141895 _141896 _141897 : Type'} (GEN_PVAR_361 : type2 _141895 _141896 _141897) (x : cart _141895 _141896) (s : type24 _141895 _141896) (y : cart _141895 _141897) (t : type24 _141895 _141897) : (term38 _141895 _141896 _141897 GEN_PVAR_361 s t x y) = (term39 _141895 _141896 _141897 GEN_PVAR_361 x s y t).
Proof. exact (MK_COMB (@lem8004008 _141895 _141896 _141897 GEN_PVAR_361) (@lem8004007 _141895 _141896 _141897 x s y t)). Qed.
Lemma lem8004010 {_141895 _141896 _141897 : Type'} (x : cart _141895 _141896) (y : cart _141895 _141897) : (@pastecart _141895 _141896 _141897 x y) = (@pastecart _141895 _141896 _141897 x y).
Proof. exact (eq_refl (@pastecart _141895 _141896 _141897 x y)). Qed.
Lemma lem8004011 {_141895 _141896 _141897 : Type'} (GEN_PVAR_361 : type2 _141895 _141896 _141897) (s : type24 _141895 _141896) (t : type24 _141895 _141897) (x : cart _141895 _141896) (y : cart _141895 _141897) : (term40 _141895 _141896 _141897 GEN_PVAR_361 s t x y) = (term41 _141895 _141896 _141897 GEN_PVAR_361 s t x y).
Proof. exact (MK_COMB (@lem8004009 _141895 _141896 _141897 GEN_PVAR_361 x s y t) (@lem8004010 _141895 _141896 _141897 x y)). Qed.
Lemma lem8004012 {_141895 _141896 _141897 : Type'} (GEN_PVAR_361 : type2 _141895 _141896 _141897) (s : type24 _141895 _141896) (t : type24 _141895 _141897) (x : cart _141895 _141896) : (term42 _141895 _141896 _141897 GEN_PVAR_361 s t x) = (term43 _141895 _141896 _141897 GEN_PVAR_361 s t x).
Proof. exact (fun_ext (fun y : cart _141895 _141897 => @lem8004011 _141895 _141896 _141897 GEN_PVAR_361 s t x y)). Qed.
Lemma lem8004013 {_141895 _141897 : Type'} : (@ex (cart _141895 _141897)) = (@ex (cart _141895 _141897)).
Proof. exact (eq_refl (@ex (cart _141895 _141897))). Qed.
Lemma lem8004014 {_141895 _141896 _141897 : Type'} (GEN_PVAR_361 : type2 _141895 _141896 _141897) (s : type24 _141895 _141896) (t : type24 _141895 _141897) (x : cart _141895 _141896) : (term44 _141895 _141896 _141897 GEN_PVAR_361 s t x) = (term45 _141895 _141896 _141897 GEN_PVAR_361 s t x).
Proof. exact (MK_COMB (@lem8004013 _141895 _141897) (@lem8004012 _141895 _141896 _141897 GEN_PVAR_361 s t x)). Qed.
Lemma lem8004015 {_141895 _141896 _141897 : Type'} (GEN_PVAR_361 : type2 _141895 _141896 _141897) (s : type24 _141895 _141896) (t : type24 _141895 _141897) : (term46 _141895 _141896 _141897 GEN_PVAR_361 s t) = (term47 _141895 _141896 _141897 GEN_PVAR_361 s t).
Proof. exact (fun_ext (fun x : cart _141895 _141896 => @lem8004014 _141895 _141896 _141897 GEN_PVAR_361 s t x)). Qed.
Lemma lem8004016 {_141895 _141896 : Type'} : (@ex (cart _141895 _141896)) = (@ex (cart _141895 _141896)).
Proof. exact (eq_refl (@ex (cart _141895 _141896))). Qed.
Lemma lem8004017 {_141895 _141896 _141897 : Type'} (GEN_PVAR_361 : type2 _141895 _141896 _141897) (s : type24 _141895 _141896) (t : type24 _141895 _141897) : (term48 _141895 _141896 _141897 GEN_PVAR_361 s t) = (term49 _141895 _141896 _141897 GEN_PVAR_361 s t).
Proof. exact (MK_COMB (@lem8004016 _141895 _141896) (@lem8004015 _141895 _141896 _141897 GEN_PVAR_361 s t)). Qed.
Lemma lem8004018 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) : (term50 _141895 _141896 _141897 s t) = (term51 _141895 _141896 _141897 s t).
Proof. exact (fun_ext (fun GEN_PVAR_361 : type2 _141895 _141896 _141897 => @lem8004017 _141895 _141896 _141897 GEN_PVAR_361 s t)). Qed.
Lemma lem8004019 {_141895 _141896 _141897 : Type'} : (@GSPEC (cart _141895 (finite_sum _141896 _141897))) = (@GSPEC (cart _141895 (finite_sum _141896 _141897))).
Proof. exact (eq_refl (@GSPEC (cart _141895 (finite_sum _141896 _141897)))). Qed.
Lemma lem8004020 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) : (term52 _141895 _141896 _141897 s t) = (term17 _141895 _141896 _141897 s t).
Proof. exact (MK_COMB (@lem8004019 _141895 _141896 _141897) (@lem8004018 _141895 _141896 _141897 s t)). Qed.
Lemma lem8004021 {_141895 _141896 _141897 : Type'} (z : type2 _141895 _141896 _141897) : (@IN (cart _141895 (finite_sum _141896 _141897)) z) = (@IN (cart _141895 (finite_sum _141896 _141897)) z).
Proof. exact (eq_refl (@IN (cart _141895 (finite_sum _141896 _141897)) z)). Qed.
Lemma lem8004022 {_141895 _141896 _141897 : Type'} (z : type2 _141895 _141896 _141897) (s : type24 _141895 _141896) (t : type24 _141895 _141897) : (term53 _141895 _141896 _141897 z s t) = (term19 _141895 _141896 _141897 z s t).
Proof. exact (MK_COMB (@lem8004021 _141895 _141896 _141897 z) (@lem8004020 _141895 _141896 _141897 s t)). Qed.
Lemma lem8004023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8004024 {_141895 _141896 _141897 : Type'} (z : type2 _141895 _141896 _141897) (s : type24 _141895 _141896) (t : type24 _141895 _141897) : (term54 _141895 _141896 _141897 z s t) = (term21 _141895 _141896 _141897 z s t).
Proof. exact (MK_COMB (@lem8004023) (@lem8004022 _141895 _141896 _141897 z s t)). Qed.
Lemma lem8004025 {_141895 _141896 _141897 : Type'} (P : type16 _141895 _141896 _141897) (z : type2 _141895 _141896 _141897) : (P z) = (P z).
Proof. exact (eq_refl (P z)). Qed.
Lemma lem8004026 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) (z : type2 _141895 _141896 _141897) : (term55 _141895 _141896 _141897 s t P z) = (term23 _141895 _141896 _141897 s t P z).
Proof. exact (MK_COMB (@lem8004024 _141895 _141896 _141897 z s t) (@lem8004025 _141895 _141896 _141897 P z)). Qed.
Lemma lem8004027 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term56 _141895 _141896 _141897 s t P) = (term25 _141895 _141896 _141897 s t P).
Proof. exact (fun_ext (fun z : type2 _141895 _141896 _141897 => @lem8004026 _141895 _141896 _141897 s t P z)). Qed.
Lemma lem8004028 {_141895 _141896 _141897 : Type'} : (@ex (cart _141895 (finite_sum _141896 _141897))) = (@ex (cart _141895 (finite_sum _141896 _141897))).
Proof. exact (eq_refl (@ex (cart _141895 (finite_sum _141896 _141897)))). Qed.
Lemma lem8004029 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term30 _141895 _141896 _141897 s t P) = (term27 _141895 _141896 _141897 s t P).
Proof. exact (MK_COMB (@lem8004028 _141895 _141896 _141897) (@lem8004027 _141895 _141896 _141897 s t P)). Qed.
Lemma lem8004030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004031 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term57 _141895 _141896 _141897 s t P) = (term58 _141895 _141896 _141897 s t P).
Proof. exact (MK_COMB (@lem8004030) (@lem8004029 _141895 _141896 _141897 s t P)). Qed.
Lemma lem8004032 {_141895 _141896 _141897 : Type'} (x : cart _141895 _141896) (s : type24 _141895 _141896) (t : type24 _141895 _141897) : (term33 _141895 _141896 _141897 s t x) = (term34 _141895 _141896 _141897 x s t).
Proof. exact (eq_refl (term33 _141895 _141896 _141897 s t x)). Qed.
Lemma lem8004033 {_141895 _141897 : Type'} (y : cart _141895 _141897) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8004034 {_141895 _141896 _141897 : Type'} (x : cart _141895 _141896) (s : type24 _141895 _141896) (t : type24 _141895 _141897) (y : cart _141895 _141897) : (term35 _141895 _141896 _141897 s t x y) = (term36 _141895 _141896 _141897 x s t y).
Proof. exact (MK_COMB (@lem8004032 _141895 _141896 _141897 x s t) (@lem8004033 _141895 _141897 y)). Qed.
Lemma lem8004035 {_141895 _141896 _141897 : Type'} (x : cart _141895 _141896) (s : type24 _141895 _141896) (y : cart _141895 _141897) (t : type24 _141895 _141897) : (term36 _141895 _141896 _141897 x s t y) = (term37 _141895 _141896 _141897 x s y t).
Proof. exact (eq_refl (term36 _141895 _141896 _141897 x s t y)). Qed.
Lemma lem8004036 {_141895 _141896 _141897 : Type'} (x : cart _141895 _141896) (s : type24 _141895 _141896) (y : cart _141895 _141897) (t : type24 _141895 _141897) : (term35 _141895 _141896 _141897 s t x y) = (term37 _141895 _141896 _141897 x s y t).
Proof. exact (TRANS (@lem8004034 _141895 _141896 _141897 x s t y) (@lem8004035 _141895 _141896 _141897 x s y t)). Qed.
Lemma lem8004037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8004038 {_141895 _141896 _141897 : Type'} (x : cart _141895 _141896) (s : type24 _141895 _141896) (y : cart _141895 _141897) (t : type24 _141895 _141897) : (term59 _141895 _141896 _141897 s t x y) = (term60 _141895 _141896 _141897 x s y t).
Proof. exact (MK_COMB (@lem8004037) (@lem8004036 _141895 _141896 _141897 x s y t)). Qed.
Lemma lem8004039 {_141895 _141896 _141897 : Type'} (P : type16 _141895 _141896 _141897) (x : cart _141895 _141896) (y : cart _141895 _141897) : (term61 _141895 _141896 _141897 P x y) = (term61 _141895 _141896 _141897 P x y).
Proof. exact (eq_refl (term61 _141895 _141896 _141897 P x y)). Qed.
Lemma lem8004040 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) (x : cart _141895 _141896) (y : cart _141895 _141897) : (term62 _141895 _141896 _141897 s t P x y) = (term63 _141895 _141896 _141897 s t P x y).
Proof. exact (MK_COMB (@lem8004038 _141895 _141896 _141897 x s y t) (@lem8004039 _141895 _141896 _141897 P x y)). Qed.
Lemma lem8004041 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) (x : cart _141895 _141896) : (term64 _141895 _141896 _141897 s t P x) = (term65 _141895 _141896 _141897 s t P x).
Proof. exact (fun_ext (fun y : cart _141895 _141897 => @lem8004040 _141895 _141896 _141897 s t P x y)). Qed.
Lemma lem8004042 {_141895 _141897 : Type'} : (@ex (cart _141895 _141897)) = (@ex (cart _141895 _141897)).
Proof. exact (eq_refl (@ex (cart _141895 _141897))). Qed.
Lemma lem8004043 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) (x : cart _141895 _141896) : (term66 _141895 _141896 _141897 s t P x) = (term67 _141895 _141896 _141897 s t P x).
Proof. exact (MK_COMB (@lem8004042 _141895 _141897) (@lem8004041 _141895 _141896 _141897 s t P x)). Qed.
Lemma lem8004044 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term68 _141895 _141896 _141897 s t P) = (term69 _141895 _141896 _141897 s t P).
Proof. exact (fun_ext (fun x : cart _141895 _141896 => @lem8004043 _141895 _141896 _141897 s t P x)). Qed.
Lemma lem8004045 {_141895 _141896 : Type'} : (@ex (cart _141895 _141896)) = (@ex (cart _141895 _141896)).
Proof. exact (eq_refl (@ex (cart _141895 _141896))). Qed.
Lemma lem8004046 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term31 _141895 _141896 _141897 s t P) = (term70 _141895 _141896 _141897 s t P).
Proof. exact (MK_COMB (@lem8004045 _141895 _141896) (@lem8004044 _141895 _141896 _141897 s t P)). Qed.
Lemma lem8004047 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : ((term30 _141895 _141896 _141897 s t P) = (term31 _141895 _141896 _141897 s t P)) = ((term27 _141895 _141896 _141897 s t P) = (term70 _141895 _141896 _141897 s t P)).
Proof. exact (MK_COMB (@lem8004031 _141895 _141896 _141897 s t P) (@lem8004046 _141895 _141896 _141897 s t P)). Qed.
Lemma lem8004048 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term27 _141895 _141896 _141897 s t P) = (term70 _141895 _141896 _141897 s t P).
Proof. exact (EQ_MP (@lem8004047 _141895 _141896 _141897 s t P) (@lem8004002 _141895 _141896 _141897 s t P)). Qed.
Lemma lem8004061 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term26 _141895 _141896 _141897 s t P) = (term70 _141895 _141896 _141897 s t P).
Proof. exact (TRANS (@lem8003998 _141895 _141896 _141897 s t P) (@lem8004048 _141895 _141896 _141897 s t P)). Qed.
Lemma lem8004062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004063 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term71 _141895 _141896 _141897 s t P) = (term72 _141895 _141896 _141897 s t P).
Proof. exact (MK_COMB (@lem8004062) (@lem8004061 _141895 _141896 _141897 s t P)). Qed.
Lemma lem8004073 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8003929 t1 t2 t3) (@lem8003928 t1 t2 t3)). Qed.
Lemma lem8004074 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) (x : cart _141895 _141896) (y : cart _141895 _141897) : (term73 _141895 _141896 _141897 s t P x y) = (term63 _141895 _141896 _141897 s t P x y).
Proof. exact (@lem8004073 (@IN (cart _141895 _141896) x s) (@IN (cart _141895 _141897) y t) (term61 _141895 _141896 _141897 P x y)). Qed.
Lemma lem8004079 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) (x : cart _141895 _141896) : (term74 _141895 _141896 _141897 s t P x) = (term65 _141895 _141896 _141897 s t P x).
Proof. exact (fun_ext (fun y : cart _141895 _141897 => @lem8004074 _141895 _141896 _141897 s t P x y)). Qed.
Lemma lem8004080 {_141895 _141897 : Type'} : (@ex (cart _141895 _141897)) = (@ex (cart _141895 _141897)).
Proof. exact (eq_refl (@ex (cart _141895 _141897))). Qed.
Lemma lem8004081 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) (x : cart _141895 _141896) : (term75 _141895 _141896 _141897 s t P x) = (term67 _141895 _141896 _141897 s t P x).
Proof. exact (MK_COMB (@lem8004080 _141895 _141897) (@lem8004079 _141895 _141896 _141897 s t P x)). Qed.
Lemma lem8004086 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term76 _141895 _141896 _141897 s t P) = (term69 _141895 _141896 _141897 s t P).
Proof. exact (fun_ext (fun x : cart _141895 _141896 => @lem8004081 _141895 _141896 _141897 s t P x)). Qed.
Lemma lem8004087 {_141895 _141896 : Type'} : (@ex (cart _141895 _141896)) = (@ex (cart _141895 _141896)).
Proof. exact (eq_refl (@ex (cart _141895 _141896))). Qed.
Lemma lem8004088 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term77 _141895 _141896 _141897 s t P) = (term70 _141895 _141896 _141897 s t P).
Proof. exact (MK_COMB (@lem8004087 _141895 _141896) (@lem8004086 _141895 _141896 _141897 s t P)). Qed.
Lemma lem8004093 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : ((term26 _141895 _141896 _141897 s t P) = (term77 _141895 _141896 _141897 s t P)) = ((term70 _141895 _141896 _141897 s t P) = (term70 _141895 _141896 _141897 s t P)).
Proof. exact (MK_COMB (@lem8004063 _141895 _141896 _141897 s t P) (@lem8004088 _141895 _141896 _141897 s t P)). Qed.
Lemma lem8004095 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8004096 (x : Prop) : (x = x) = True.
Proof. exact (@lem8004095 Prop x). Qed.
Lemma lem8004097 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : ((term70 _141895 _141896 _141897 s t P) = (term70 _141895 _141896 _141897 s t P)) = True.
Proof. exact (@lem8004096 (term70 _141895 _141896 _141897 s t P)). Qed.
Lemma lem8004098 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : ((term26 _141895 _141896 _141897 s t P) = (term77 _141895 _141896 _141897 s t P)) = True.
Proof. exact (TRANS (@lem8004093 _141895 _141896 _141897 s t P) (@lem8004097 _141895 _141896 _141897 s t P)). Qed.
Lemma lem8004099 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : True = ((term26 _141895 _141896 _141897 s t P) = (term77 _141895 _141896 _141897 s t P)).
Proof. exact (SYM (@lem8004098 _141895 _141896 _141897 s t P)). Qed.

Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL_IMP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem1120973 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1120974 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1120975 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1120974 t1) (@lem1120973 t1)). Qed.
Lemma lem1120976 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1120975 t1 t2). Qed.
Lemma lem1120977 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1120978 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1120977 t1 t2) (@lem1120976 t1 t2)). Qed.
Lemma lem1120979 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1120978 t1 t2 t3). Qed.
Lemma lem1120980 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1120981 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1120980 t1 t2 t3) (@lem1120979 t1 t2 t3)). Qed.
Lemma lem1120982 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1120981 t1 t2 t3)). Qed.
Lemma lem1120988 {A : Type'} (P : type1143 A) : term7 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1120989 {_26340 : Type'} (P : type1143 _26340) : term7 _26340 P.
Proof. exact (@lem1120988 _26340 P). Qed.
Lemma lem1120990 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : term8 _26340 P Q.
Proof. exact (@lem1120989 _26340 (term9 _26340 P Q)). Qed.
Lemma lem1120991 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term10 _26340 P Q) = (term11 _26340 P Q).
Proof. exact (eq_refl (term10 _26340 P Q)). Qed.
Lemma lem1120992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1120993 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term12 _26340 P Q) = (term13 _26340 P Q).
Proof. exact (MK_COMB (@lem1120992) (@lem1120991 _26340 P Q)). Qed.
Lemma lem1120994 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term14 _26340 P Q t) = (term15 _26340 P Q t).
Proof. exact (eq_refl (term14 _26340 P Q t)). Qed.
Lemma lem1120995 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1120996 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term16 _26340 P Q t) = (term17 _26340 P Q t).
Proof. exact (MK_COMB (@lem1120995) (@lem1120994 _26340 P Q t)). Qed.
Lemma lem1120997 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (h : _26340) (t : list _26340) : (term18 _26340 P Q h t) = (term19 _26340 P Q h t).
Proof. exact (eq_refl (term18 _26340 P Q h t)). Qed.
Lemma lem1120998 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (h : _26340) (t : list _26340) : (term20 _26340 P Q h t) = (term21 _26340 P Q h t).
Proof. exact (MK_COMB (@lem1120996 _26340 P Q t) (@lem1120997 _26340 P Q h t)). Qed.
Lemma lem1120999 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (h : _26340) : (term22 _26340 P Q h) = (term23 _26340 P Q h).
Proof. exact (fun_ext (fun t : list _26340 => @lem1120998 _26340 P Q h t)). Qed.
Lemma lem1121000 {_26340 : Type'} : (@all (list _26340)) = (@all (list _26340)).
Proof. exact (eq_refl (@all (list _26340))). Qed.
Lemma lem1121001 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (h : _26340) : (term24 _26340 P Q h) = (term25 _26340 P Q h).
Proof. exact (MK_COMB (@lem1121000 _26340) (@lem1120999 _26340 P Q h)). Qed.
Lemma lem1121002 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term26 _26340 P Q) = (term27 _26340 P Q).
Proof. exact (fun_ext (fun h : _26340 => @lem1121001 _26340 P Q h)). Qed.
Lemma lem1121003 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1121004 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term28 _26340 P Q) = (term29 _26340 P Q).
Proof. exact (MK_COMB (@lem1121003 _26340) (@lem1121002 _26340 P Q)). Qed.
Lemma lem1121005 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term30 _26340 P Q) = (term31 _26340 P Q).
Proof. exact (MK_COMB (@lem1120993 _26340 P Q) (@lem1121004 _26340 P Q)). Qed.
Lemma lem1121006 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1121007 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term32 _26340 P Q) = (term33 _26340 P Q).
Proof. exact (MK_COMB (@lem1121006) (@lem1121005 _26340 P Q)). Qed.
Lemma lem1121008 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (l : list _26340) : (term14 _26340 P Q l) = (term15 _26340 P Q l).
Proof. exact (eq_refl (term14 _26340 P Q l)). Qed.
Lemma lem1121009 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term34 _26340 P Q) = (term9 _26340 P Q).
Proof. exact (fun_ext (fun l : list _26340 => @lem1121008 _26340 P Q l)). Qed.
Lemma lem1121010 {_26340 : Type'} : (@all (list _26340)) = (@all (list _26340)).
Proof. exact (eq_refl (@all (list _26340))). Qed.
Lemma lem1121011 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term35 _26340 P Q) = (term36 _26340 P Q).
Proof. exact (MK_COMB (@lem1121010 _26340) (@lem1121009 _26340 P Q)). Qed.
Lemma lem1121012 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term8 _26340 P Q) = (term37 _26340 P Q).
Proof. exact (MK_COMB (@lem1121007 _26340 P Q) (@lem1121011 _26340 P Q)). Qed.
Lemma lem1121013 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : term37 _26340 P Q.
Proof. exact (EQ_MP (@lem1121012 _26340 P Q) (@lem1120990 _26340 P Q)). Qed.
Lemma lem1121014 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term15 _26340 P Q t) : term15 _26340 P Q t.
Proof. exact (h1). Qed.
Lemma lem1121028 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1121029 {_26340 : Type'} (x : _26340) : (@List.In _26340 x (@nil _26340)) = False.
Proof. exact (@lem1121028 _26340 x). Qed.
Lemma lem1121030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1121031 {_26340 : Type'} (x : _26340) : (term38 _26340 x) = (and False).
Proof. exact (MK_COMB (@lem1121030) (@lem1121029 _26340 x)). Qed.
Lemma lem1121032 {_26340 : Type'} (P : _26340 -> Prop) (x : _26340) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1121033 {_26340 : Type'} (P : _26340 -> Prop) (x : _26340) : (term39 _26340 P x) = (term40 _26340 P x).
Proof. exact (MK_COMB (@lem1121031 _26340 x) (@lem1121032 _26340 P x)). Qed.
Lemma lem1121035 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1121036 {_26340 : Type'} (P : _26340 -> Prop) (x : _26340) : (term40 _26340 P x) = False.
Proof. exact (@lem1121035 (P x)). Qed.
Lemma lem1121037 {_26340 : Type'} (P : _26340 -> Prop) (x : _26340) : (term39 _26340 P x) = False.
Proof. exact (TRANS (@lem1121033 _26340 P x) (@lem1121036 _26340 P x)). Qed.
Lemma lem1121038 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1121039 {_26340 : Type'} (P : _26340 -> Prop) (x : _26340) : (term41 _26340 P x) = (imp False).
Proof. exact (MK_COMB (@lem1121038) (@lem1121037 _26340 P x)). Qed.
Lemma lem1121040 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) : (Q x) = (Q x).
Proof. exact (eq_refl (Q x)). Qed.
Lemma lem1121041 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term42 _26340 P Q x) = (term43 _26340 Q x).
Proof. exact (MK_COMB (@lem1121039 _26340 P x) (@lem1121040 _26340 Q x)). Qed.
Lemma lem1121043 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1121044 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) : (term43 _26340 Q x) = True.
Proof. exact (@lem1121043 (Q x)). Qed.
Lemma lem1121045 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term42 _26340 P Q x) = True.
Proof. exact (TRANS (@lem1121041 _26340 P Q x) (@lem1121044 _26340 Q x)). Qed.
Lemma lem1121046 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term44 _26340 P Q) = (term45 _26340).
Proof. exact (fun_ext (fun x : _26340 => @lem1121045 _26340 P Q x)). Qed.
Lemma lem1121047 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1121048 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term46 _26340 P Q) = (term47 _26340).
Proof. exact (MK_COMB (@lem1121047 _26340) (@lem1121046 _26340 P Q)). Qed.
Lemma lem1121050 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1121051 {_26340 : Type'} (t : Prop) : (term48 _26340 t) = t.
Proof. exact (@lem1121050 _26340 t). Qed.
Lemma lem1121052 {_26340 : Type'} : (term47 _26340) = True.
Proof. exact (@lem1121051 _26340 True). Qed.
Lemma lem1121053 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term46 _26340 P Q) = True.
Proof. exact (TRANS (@lem1121048 _26340 P Q) (@lem1121052 _26340)). Qed.
Lemma lem1121054 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1121055 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term49 _26340 P Q) = (and True).
Proof. exact (MK_COMB (@lem1121054) (@lem1121053 _26340 P Q)). Qed.
Lemma lem1121057 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1121058 {_26340 : Type'} (P : _26340 -> Prop) : (@List.Forall _26340 P (@nil _26340)) = True.
Proof. exact (@lem1121057 _26340 P). Qed.
Lemma lem1121059 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) : (term50 _26340 Q P) = (True /\ True).
Proof. exact (MK_COMB (@lem1121055 _26340 P Q) (@lem1121058 _26340 P)). Qed.
Lemma lem1121061 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1121062 : (True /\ True) = True.
Proof. exact (@lem1121061 True). Qed.
Lemma lem1121063 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) : (term50 _26340 Q P) = True.
Proof. exact (TRANS (@lem1121059 _26340 Q P) (@lem1121062)). Qed.
Lemma lem1121064 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1121065 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) : (term51 _26340 Q P) = (imp True).
Proof. exact (MK_COMB (@lem1121064) (@lem1121063 _26340 Q P)). Qed.
Lemma lem1121067 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1121068 {_26340 : Type'} (P : _26340 -> Prop) : (@List.Forall _26340 P (@nil _26340)) = True.
Proof. exact (@lem1121067 _26340 P). Qed.
Lemma lem1121069 {_26340 : Type'} (Q : _26340 -> Prop) : (@List.Forall _26340 Q (@nil _26340)) = True.
Proof. exact (@lem1121068 _26340 Q). Qed.
Lemma lem1121070 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term11 _26340 P Q) = (True -> True).
Proof. exact (MK_COMB (@lem1121065 _26340 Q P) (@lem1121069 _26340 Q)). Qed.
Lemma lem1121072 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1121073 : (True -> True) = True.
Proof. exact (@lem1121072 True). Qed.
Lemma lem1121074 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term11 _26340 P Q) = True.
Proof. exact (TRANS (@lem1121070 _26340 P Q) (@lem1121073)). Qed.
Lemma lem1121075 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : True = (term11 _26340 P Q).
Proof. exact (SYM (@lem1121074 _26340 P Q)). Qed.
Lemma lem1121076 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : term11 _26340 P Q.
Proof. exact (EQ_MP (@lem1121075 _26340 P Q) (@lem0)). Qed.
Lemma lem1121090 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term52 _25376 x h t) = (term53 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1121091 {_26340 : Type'} (h : _26340) (x : _26340) (t : list _26340) : (term52 _26340 x h t) = (term53 _26340 h x t).
Proof. exact (@lem1121090 _26340 h x t). Qed.
Lemma lem1121096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1121097 {_26340 : Type'} (h : _26340) (x : _26340) (t : list _26340) : (term54 _26340 x h t) = (term55 _26340 h x t).
Proof. exact (MK_COMB (@lem1121096) (@lem1121091 _26340 h x t)). Qed.
Lemma lem1121098 {_26340 : Type'} (P : _26340 -> Prop) (x : _26340) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1121099 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term56 _26340 h t P x) = (term57 _26340 h t P x).
Proof. exact (MK_COMB (@lem1121097 _26340 h x t) (@lem1121098 _26340 P x)). Qed.
Lemma lem1121102 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1121103 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term58 _26340 h t P x) = (term59 _26340 h t P x).
Proof. exact (MK_COMB (@lem1121102) (@lem1121099 _26340 h t P x)). Qed.
Lemma lem1121104 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) : (Q x) = (Q x).
Proof. exact (eq_refl (Q x)). Qed.
Lemma lem1121105 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term60 _26340 h t P Q x) = (term61 _26340 h t P Q x).
Proof. exact (MK_COMB (@lem1121103 _26340 h t P x) (@lem1121104 _26340 Q x)). Qed.
Lemma lem1121108 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term62 _26340 h t P Q) = (term63 _26340 h t P Q).
Proof. exact (fun_ext (fun x : _26340 => @lem1121105 _26340 h t P Q x)). Qed.
Lemma lem1121109 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1121110 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term64 _26340 h t P Q) = (term65 _26340 h t P Q).
Proof. exact (MK_COMB (@lem1121109 _26340) (@lem1121108 _26340 h t P Q)). Qed.
Lemma lem1121115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1121116 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term66 _26340 h t P Q) = (term67 _26340 h t P Q).
Proof. exact (MK_COMB (@lem1121115) (@lem1121110 _26340 h t P Q)). Qed.
Lemma lem1121118 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term68 _25307 P h t) = (term69 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1121119 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (t : list _26340) : (term68 _26340 P h t) = (term69 _26340 h P t).
Proof. exact (@lem1121118 _26340 h P t). Qed.
Lemma lem1121122 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) : (term70 _26340 Q P h t) = (term71 _26340 Q h P t).
Proof. exact (MK_COMB (@lem1121116 _26340 h t P Q) (@lem1121119 _26340 h P t)). Qed.
Lemma lem1121125 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1121126 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) : (term72 _26340 Q P h t) = (term73 _26340 Q h P t).
Proof. exact (MK_COMB (@lem1121125) (@lem1121122 _26340 Q h P t)). Qed.
Lemma lem1121128 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term68 _25307 P h t) = (term69 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1121129 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (t : list _26340) : (term68 _26340 P h t) = (term69 _26340 h P t).
Proof. exact (@lem1121128 _26340 h P t). Qed.
Lemma lem1121130 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term68 _26340 Q h t) = (term69 _26340 h Q t).
Proof. exact (@lem1121129 _26340 h Q t). Qed.
Lemma lem1121133 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term19 _26340 P Q h t) = (term74 _26340 P h Q t).
Proof. exact (MK_COMB (@lem1121126 _26340 Q h P t) (@lem1121130 _26340 h Q t)). Qed.
Lemma lem1121136 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (h : _26340) (t : list _26340) : (term74 _26340 P h Q t) = (term19 _26340 P Q h t).
Proof. exact (SYM (@lem1121133 _26340 P h Q t)). Qed.
Lemma lem1121138 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1121139 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term74 _26340 P h Q t) = (term76 _26340 P h Q t).
Proof. exact (@lem1121138 (term74 _26340 P h Q t)). Qed.
Lemma lem1121140 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term76 _26340 P h Q t) = (term74 _26340 P h Q t).
Proof. exact (SYM (@lem1121139 _26340 P h Q t)). Qed.
Lemma lem1121141 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (h1 : term77 _26340 P h Q t) : term77 _26340 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1121144 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (h1 : term78 _26340 P h Q t) : term78 _26340 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1121145 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : term79 _26340 P h Q t.
Proof. exact (fun h0 : term78 _26340 P h Q t => @lem1121144 _26340 P h Q t h0). Qed.
Lemma lem1121146 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (h1 : term79 _26340 P h Q t) : term79 _26340 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1121147 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (h1 : term78 _26340 P h Q t) : term78 _26340 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1121148 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (h1 : term78 _26340 P h Q t) (h2 : term79 _26340 P h Q t) : term78 _26340 P h Q t.
Proof. exact (@lem1121146 _26340 P h Q t h2 (@lem1121147 _26340 P h Q t h1)). Qed.
Lemma lem1121149 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (h1 : term78 _26340 P h Q t) : term80 _26340 P h Q t.
Proof. exact (fun h0 : term79 _26340 P h Q t => @lem1121148 _26340 P h Q t h1 h0). Qed.
Lemma lem1121150 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (h1 : term79 _26340 P h Q t) : term79 _26340 P h Q t.
Proof. exact (h1). Qed.
Lemma lem1121151 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (h1 : term78 _26340 P h Q t) (h2 : term79 _26340 P h Q t) : term78 _26340 P h Q t.
Proof. exact (@lem1121149 _26340 P h Q t h1 (@lem1121150 _26340 P h Q t h2)). Qed.
Lemma lem1121152 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (h1 : term79 _26340 P h Q t) : term79 _26340 P h Q t.
Proof. exact (fun h0 : term78 _26340 P h Q t => @lem1121151 _26340 P h Q t h0 h1). Qed.
Lemma lem1121153 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : term81 _26340 P h Q t.
Proof. exact (fun h0 : term79 _26340 P h Q t => @lem1121152 _26340 P h Q t h0). Qed.
Lemma lem1121156 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : term79 _26340 P h Q t.
Proof. exact (@lem1121153 _26340 P h Q t (@lem1121145 _26340 P h Q t)). Qed.
Lemma lem1121157 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : term79 _26340 P h Q t.
Proof. exact (@lem1121156 _26340 P h Q t). Qed.
Lemma lem1121189 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1121190 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term76 _26340 P h Q t) = (term82 _26340 P h Q t).
Proof. exact (@lem1121189 (term77 _26340 P h Q t)). Qed.
Lemma lem1121192 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1121193 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term82 _26340 P h Q t) = (term74 _26340 P h Q t).
Proof. exact (@lem1121192 (term74 _26340 P h Q t)). Qed.
Lemma lem1121196 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term76 _26340 P h Q t) = (term74 _26340 P h Q t).
Proof. exact (TRANS (@lem1121190 _26340 P h Q t) (@lem1121193 _26340 P h Q t)). Qed.
Lemma lem1121213 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term17 _26340 P Q t) = (term17 _26340 P Q t).
Proof. exact (eq_refl (term17 _26340 P Q t)). Qed.
Lemma lem1121214 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term78 _26340 P h Q t) = (term84 _26340 P h Q t).
Proof. exact (MK_COMB (@lem1121213 _26340 P Q t) (@lem1121196 _26340 P h Q t)). Qed.
Lemma lem1121217 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term85 _26340 h Q t) = (term86 _26340 h Q t).
Proof. exact (fun_ext (fun P : _26340 -> Prop => @lem1121214 _26340 P h Q t)). Qed.
Lemma lem1121218 {_26340 : Type'} : (@all (_26340 -> Prop)) = (@all (_26340 -> Prop)).
Proof. exact (eq_refl (@all (_26340 -> Prop))). Qed.
Lemma lem1121219 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term87 _26340 h Q t) = (term88 _26340 h Q t).
Proof. exact (MK_COMB (@lem1121218 _26340) (@lem1121217 _26340 h Q t)). Qed.
Lemma lem1121224 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (term89 _26340 Q t) = (term90 _26340 Q t).
Proof. exact (fun_ext (fun h : _26340 => @lem1121219 _26340 h Q t)). Qed.
Lemma lem1121225 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1121226 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (term91 _26340 Q t) = (term92 _26340 Q t).
Proof. exact (MK_COMB (@lem1121225 _26340) (@lem1121224 _26340 Q t)). Qed.
Lemma lem1121231 {_26340 : Type'} (t : list _26340) : (term93 _26340 t) = (term94 _26340 t).
Proof. exact (fun_ext (fun Q : _26340 -> Prop => @lem1121226 _26340 Q t)). Qed.
Lemma lem1121232 {_26340 : Type'} : (@all (_26340 -> Prop)) = (@all (_26340 -> Prop)).
Proof. exact (eq_refl (@all (_26340 -> Prop))). Qed.
Lemma lem1121233 {_26340 : Type'} (t : list _26340) : (term95 _26340 t) = (term96 _26340 t).
Proof. exact (MK_COMB (@lem1121232 _26340) (@lem1121231 _26340 t)). Qed.
Lemma lem1121238 {_26340 : Type'} : (term97 _26340) = (term98 _26340).
Proof. exact (fun_ext (fun t : list _26340 => @lem1121233 _26340 t)). Qed.
Lemma lem1121239 {_26340 : Type'} : (@all (list _26340)) = (@all (list _26340)).
Proof. exact (eq_refl (@all (list _26340))). Qed.
Lemma lem1121248 {_26340 : Type'} : (term99 _26340) = (term100 _26340).
Proof. exact (MK_COMB (@lem1121239 _26340) (@lem1121238 _26340)). Qed.
Lemma lem1121253 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term69 _26340 h Q t) = (term69 _26340 h Q t).
Proof. exact (eq_refl (term69 _26340 h Q t)). Qed.
Lemma lem1121258 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (t : list _26340) : (term69 _26340 h P t) = (term69 _26340 h P t).
Proof. exact (eq_refl (term69 _26340 h P t)). Qed.
Lemma lem1121271 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term61 _26340 h t P Q x) = (term61 _26340 h t P Q x).
Proof. exact (eq_refl (term61 _26340 h t P Q x)). Qed.
Lemma lem1121272 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term63 _26340 h t P Q) = (term63 _26340 h t P Q).
Proof. exact (fun_ext (fun x : _26340 => @lem1121271 _26340 h t P Q x)). Qed.
Lemma lem1121273 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1121274 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term65 _26340 h t P Q) = (term65 _26340 h t P Q).
Proof. exact (MK_COMB (@lem1121273 _26340) (@lem1121272 _26340 h t P Q)). Qed.
Lemma lem1121275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1121276 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term67 _26340 h t P Q) = (term67 _26340 h t P Q).
Proof. exact (MK_COMB (@lem1121275) (@lem1121274 _26340 h t P Q)). Qed.
Lemma lem1121277 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) : (term71 _26340 Q h P t) = (term71 _26340 Q h P t).
Proof. exact (MK_COMB (@lem1121276 _26340 h t P Q) (@lem1121258 _26340 h P t)). Qed.
Lemma lem1121278 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1121279 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) : (term73 _26340 Q h P t) = (term73 _26340 Q h P t).
Proof. exact (MK_COMB (@lem1121278) (@lem1121277 _26340 Q h P t)). Qed.
Lemma lem1121280 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term74 _26340 P h Q t) = (term74 _26340 P h Q t).
Proof. exact (MK_COMB (@lem1121279 _26340 Q h P t) (@lem1121253 _26340 h Q t)). Qed.
Lemma lem1121281 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (@List.Forall _26340 Q t) = (@List.Forall _26340 Q t).
Proof. exact (eq_refl (@List.Forall _26340 Q t)). Qed.
Lemma lem1121282 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) : (@List.Forall _26340 P t) = (@List.Forall _26340 P t).
Proof. exact (eq_refl (@List.Forall _26340 P t)). Qed.
Lemma lem1121291 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term101 _26340 t P Q x) = (term101 _26340 t P Q x).
Proof. exact (eq_refl (term101 _26340 t P Q x)). Qed.
Lemma lem1121292 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term102 _26340 t P Q) = (term102 _26340 t P Q).
Proof. exact (fun_ext (fun x : _26340 => @lem1121291 _26340 t P Q x)). Qed.
Lemma lem1121293 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1121294 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term103 _26340 t P Q) = (term103 _26340 t P Q).
Proof. exact (MK_COMB (@lem1121293 _26340) (@lem1121292 _26340 t P Q)). Qed.
Lemma lem1121295 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1121296 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term104 _26340 t P Q) = (term104 _26340 t P Q).
Proof. exact (MK_COMB (@lem1121295) (@lem1121294 _26340 t P Q)). Qed.
Lemma lem1121297 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term105 _26340 Q P t) = (term105 _26340 Q P t).
Proof. exact (MK_COMB (@lem1121296 _26340 t P Q) (@lem1121282 _26340 P t)). Qed.
Lemma lem1121298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1121299 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term106 _26340 Q P t) = (term106 _26340 Q P t).
Proof. exact (MK_COMB (@lem1121298) (@lem1121297 _26340 Q P t)). Qed.
Lemma lem1121300 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term15 _26340 P Q t) = (term15 _26340 P Q t).
Proof. exact (MK_COMB (@lem1121299 _26340 Q P t) (@lem1121281 _26340 Q t)). Qed.
Lemma lem1121301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1121302 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term17 _26340 P Q t) = (term17 _26340 P Q t).
Proof. exact (MK_COMB (@lem1121301) (@lem1121300 _26340 P Q t)). Qed.
Lemma lem1121303 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term84 _26340 P h Q t) = (term84 _26340 P h Q t).
Proof. exact (MK_COMB (@lem1121302 _26340 P Q t) (@lem1121280 _26340 P h Q t)). Qed.
Lemma lem1121304 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term86 _26340 h Q t) = (term86 _26340 h Q t).
Proof. exact (fun_ext (fun P : _26340 -> Prop => @lem1121303 _26340 P h Q t)). Qed.
Lemma lem1121305 {_26340 : Type'} : (@all (_26340 -> Prop)) = (@all (_26340 -> Prop)).
Proof. exact (eq_refl (@all (_26340 -> Prop))). Qed.
Lemma lem1121306 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term88 _26340 h Q t) = (term88 _26340 h Q t).
Proof. exact (MK_COMB (@lem1121305 _26340) (@lem1121304 _26340 h Q t)). Qed.
Lemma lem1121307 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (term90 _26340 Q t) = (term90 _26340 Q t).
Proof. exact (fun_ext (fun h : _26340 => @lem1121306 _26340 h Q t)). Qed.
Lemma lem1121308 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1121309 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (term92 _26340 Q t) = (term92 _26340 Q t).
Proof. exact (MK_COMB (@lem1121308 _26340) (@lem1121307 _26340 Q t)). Qed.
Lemma lem1121310 {_26340 : Type'} (t : list _26340) : (term94 _26340 t) = (term94 _26340 t).
Proof. exact (fun_ext (fun Q : _26340 -> Prop => @lem1121309 _26340 Q t)). Qed.
Lemma lem1121311 {_26340 : Type'} : (@all (_26340 -> Prop)) = (@all (_26340 -> Prop)).
Proof. exact (eq_refl (@all (_26340 -> Prop))). Qed.
Lemma lem1121312 {_26340 : Type'} (t : list _26340) : (term96 _26340 t) = (term96 _26340 t).
Proof. exact (MK_COMB (@lem1121311 _26340) (@lem1121310 _26340 t)). Qed.
Lemma lem1121313 {_26340 : Type'} : (term98 _26340) = (term98 _26340).
Proof. exact (fun_ext (fun t : list _26340 => @lem1121312 _26340 t)). Qed.
Lemma lem1121314 {_26340 : Type'} : (@all (list _26340)) = (@all (list _26340)).
Proof. exact (eq_refl (@all (list _26340))). Qed.
Lemma lem1121315 {_26340 : Type'} : (term100 _26340) = (term100 _26340).
Proof. exact (MK_COMB (@lem1121314 _26340) (@lem1121313 _26340)). Qed.
Lemma lem1121378 {_26340 : Type'} : (term99 _26340) = (term100 _26340).
Proof. exact (TRANS (@lem1121248 _26340) (@lem1121315 _26340)). Qed.
Lemma lem1121379 {_26340 : Type'} : (term100 _26340) = (term99 _26340).
Proof. exact (SYM (@lem1121378 _26340)). Qed.
Lemma lem1121380 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term15 _26340 P Q t) : term15 _26340 P Q t.
Proof. exact (h1). Qed.
Lemma lem1121381 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term71 _26340 Q h P t.
Proof. exact (h1). Qed.
Lemma lem1121383 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1121384 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term69 _26340 h Q t) = (term107 _26340 h Q t).
Proof. exact (@lem1121383 (term69 _26340 h Q t)). Qed.
Lemma lem1121385 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term107 _26340 h Q t) = (term69 _26340 h Q t).
Proof. exact (SYM (@lem1121384 _26340 h Q t)). Qed.
Lemma lem1121386 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (h1 : term108 _26340 h Q t) : term108 _26340 h Q t.
Proof. exact (h1). Qed.
Lemma lem1121397 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term109 _26340 t P Q x) = (term110 _26340 t P Q x).
Proof. exact (@lem17362 (term111 _26340 t P x) (Q x)). Qed.
Lemma lem1121398 {_26340 : Type'} (P : _26340 -> Prop) : (term112 _26340 P) = (term113 _26340 P).
Proof. exact (@lem18392 _26340 P). Qed.
Lemma lem1121399 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term114 _26340 t P Q) = (term115 _26340 t P Q).
Proof. exact (@lem1121398 _26340 (term102 _26340 t P Q)). Qed.
Lemma lem1121400 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term116 _26340 t P Q x) = (term101 _26340 t P Q x).
Proof. exact (eq_refl (term116 _26340 t P Q x)). Qed.
Lemma lem1121401 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1121402 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term117 _26340 t P Q x) = (term109 _26340 t P Q x).
Proof. exact (MK_COMB (@lem1121401) (@lem1121400 _26340 t P Q x)). Qed.
Lemma lem1121403 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term117 _26340 t P Q x) = (term110 _26340 t P Q x).
Proof. exact (TRANS (@lem1121402 _26340 t P Q x) (@lem1121397 _26340 t P Q x)). Qed.
Lemma lem1121404 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term118 _26340 t P Q) = (term119 _26340 t P Q).
Proof. exact (fun_ext (fun x : _26340 => @lem1121403 _26340 t P Q x)). Qed.
Lemma lem1121405 {_26340 : Type'} : (@ex _26340) = (@ex _26340).
Proof. exact (eq_refl (@ex _26340)). Qed.
Lemma lem1121406 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term115 _26340 t P Q) = (term120 _26340 t P Q).
Proof. exact (MK_COMB (@lem1121405 _26340) (@lem1121404 _26340 t P Q)). Qed.
Lemma lem1121407 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term114 _26340 t P Q) = (term120 _26340 t P Q).
Proof. exact (TRANS (@lem1121399 _26340 t P Q) (@lem1121406 _26340 t P Q)). Qed.
Lemma lem1121408 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) : (term121 _26340 P t) = (term121 _26340 P t).
Proof. exact (eq_refl (term121 _26340 P t)). Qed.
Lemma lem1121409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121410 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term122 _26340 t P Q) = (term123 _26340 t P Q).
Proof. exact (MK_COMB (@lem1121409) (@lem1121407 _26340 t P Q)). Qed.
Lemma lem1121411 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term124 _26340 Q P t) = (term125 _26340 Q P t).
Proof. exact (MK_COMB (@lem1121410 _26340 t P Q) (@lem1121408 _26340 P t)). Qed.
Lemma lem1121412 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term126 _26340 Q P t) = (term124 _26340 Q P t).
Proof. exact (@lem17045 (term103 _26340 t P Q) (@List.Forall _26340 P t)). Qed.
Lemma lem1121413 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term126 _26340 Q P t) = (term125 _26340 Q P t).
Proof. exact (TRANS (@lem1121412 _26340 Q P t) (@lem1121411 _26340 Q P t)). Qed.
Lemma lem1121414 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (@List.Forall _26340 Q t) = (@List.Forall _26340 Q t).
Proof. exact (eq_refl (@List.Forall _26340 Q t)). Qed.
Lemma lem1121415 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121416 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term127 _26340 Q P t) = (term128 _26340 Q P t).
Proof. exact (MK_COMB (@lem1121415) (@lem1121413 _26340 Q P t)). Qed.
Lemma lem1121417 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term129 _26340 P Q t) = (term130 _26340 P Q t).
Proof. exact (MK_COMB (@lem1121416 _26340 Q P t) (@lem1121414 _26340 Q t)). Qed.
Lemma lem1121418 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term15 _26340 P Q t) = (term129 _26340 P Q t).
Proof. exact (@lem17265 (term105 _26340 Q P t) (@List.Forall _26340 Q t)). Qed.
Lemma lem1121419 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term15 _26340 P Q t) = (term130 _26340 P Q t).
Proof. exact (TRANS (@lem1121418 _26340 P Q t) (@lem1121417 _26340 P Q t)). Qed.
Lemma lem1121470 {A : Type'} (P : A -> Prop) (Q : Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1121471 {_26340 : Type'} (P : _26340 -> Prop) (Q : Prop) : (term131 _26340 P Q) = (term132 _26340 P Q).
Proof. exact (@lem1121470 _26340 P Q). Qed.
Lemma lem1121472 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term133 _26340 Q P t) = (term134 _26340 Q P t).
Proof. exact (@lem1121471 _26340 (term119 _26340 t P Q) (term121 _26340 P t)). Qed.
Lemma lem1121473 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term135 _26340 t P Q x) = (term110 _26340 t P Q x).
Proof. exact (eq_refl (term135 _26340 t P Q x)). Qed.
Lemma lem1121474 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term136 _26340 t P Q) = (term119 _26340 t P Q).
Proof. exact (fun_ext (fun x : _26340 => @lem1121473 _26340 t P Q x)). Qed.
Lemma lem1121475 {_26340 : Type'} : (@ex _26340) = (@ex _26340).
Proof. exact (eq_refl (@ex _26340)). Qed.
Lemma lem1121476 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term137 _26340 t P Q) = (term120 _26340 t P Q).
Proof. exact (MK_COMB (@lem1121475 _26340) (@lem1121474 _26340 t P Q)). Qed.
Lemma lem1121477 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121478 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term138 _26340 t P Q) = (term123 _26340 t P Q).
Proof. exact (MK_COMB (@lem1121477) (@lem1121476 _26340 t P Q)). Qed.
Lemma lem1121479 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) : (term121 _26340 P t) = (term121 _26340 P t).
Proof. exact (eq_refl (term121 _26340 P t)). Qed.
Lemma lem1121480 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term133 _26340 Q P t) = (term125 _26340 Q P t).
Proof. exact (MK_COMB (@lem1121478 _26340 t P Q) (@lem1121479 _26340 P t)). Qed.
Lemma lem1121481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1121482 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term139 _26340 Q P t) = (term140 _26340 Q P t).
Proof. exact (MK_COMB (@lem1121481) (@lem1121480 _26340 Q P t)). Qed.
Lemma lem1121483 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term135 _26340 t P Q x) = (term110 _26340 t P Q x).
Proof. exact (eq_refl (term135 _26340 t P Q x)). Qed.
Lemma lem1121484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121485 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term141 _26340 t P Q x) = (term142 _26340 t P Q x).
Proof. exact (MK_COMB (@lem1121484) (@lem1121483 _26340 t P Q x)). Qed.
Lemma lem1121486 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) : (term121 _26340 P t) = (term121 _26340 P t).
Proof. exact (eq_refl (term121 _26340 P t)). Qed.
Lemma lem1121487 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) (P : _26340 -> Prop) (t : list _26340) : (term143 _26340 Q x P t) = (term144 _26340 Q x P t).
Proof. exact (MK_COMB (@lem1121485 _26340 t P Q x) (@lem1121486 _26340 P t)). Qed.
Lemma lem1121488 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term145 _26340 Q P t) = (term146 _26340 Q P t).
Proof. exact (fun_ext (fun x : _26340 => @lem1121487 _26340 Q x P t)). Qed.
Lemma lem1121489 {_26340 : Type'} : (@ex _26340) = (@ex _26340).
Proof. exact (eq_refl (@ex _26340)). Qed.
Lemma lem1121490 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term134 _26340 Q P t) = (term147 _26340 Q P t).
Proof. exact (MK_COMB (@lem1121489 _26340) (@lem1121488 _26340 Q P t)). Qed.
Lemma lem1121491 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : ((term133 _26340 Q P t) = (term134 _26340 Q P t)) = ((term125 _26340 Q P t) = (term147 _26340 Q P t)).
Proof. exact (MK_COMB (@lem1121482 _26340 Q P t) (@lem1121490 _26340 Q P t)). Qed.
Lemma lem1121492 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term125 _26340 Q P t) = (term147 _26340 Q P t).
Proof. exact (EQ_MP (@lem1121491 _26340 Q P t) (@lem1121472 _26340 Q P t)). Qed.
Lemma lem1121493 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121494 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term128 _26340 Q P t) = (term148 _26340 Q P t).
Proof. exact (MK_COMB (@lem1121493) (@lem1121492 _26340 Q P t)). Qed.
Lemma lem1121495 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (@List.Forall _26340 Q t) = (@List.Forall _26340 Q t).
Proof. exact (eq_refl (@List.Forall _26340 Q t)). Qed.
Lemma lem1121496 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term130 _26340 P Q t) = (term149 _26340 P Q t).
Proof. exact (MK_COMB (@lem1121494 _26340 Q P t) (@lem1121495 _26340 Q t)). Qed.
Lemma lem1121498 {A : Type'} (P : A -> Prop) (Q : Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1121499 {_26340 : Type'} (P : _26340 -> Prop) (Q : Prop) : (term131 _26340 P Q) = (term132 _26340 P Q).
Proof. exact (@lem1121498 _26340 P Q). Qed.
Lemma lem1121500 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term150 _26340 P Q t) = (term151 _26340 P Q t).
Proof. exact (@lem1121499 _26340 (term146 _26340 Q P t) (@List.Forall _26340 Q t)). Qed.
Lemma lem1121501 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) (P : _26340 -> Prop) (t : list _26340) : (term152 _26340 Q P t x) = (term144 _26340 Q x P t).
Proof. exact (eq_refl (term152 _26340 Q P t x)). Qed.
Lemma lem1121502 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term153 _26340 Q P t) = (term146 _26340 Q P t).
Proof. exact (fun_ext (fun x : _26340 => @lem1121501 _26340 Q x P t)). Qed.
Lemma lem1121503 {_26340 : Type'} : (@ex _26340) = (@ex _26340).
Proof. exact (eq_refl (@ex _26340)). Qed.
Lemma lem1121504 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term154 _26340 Q P t) = (term147 _26340 Q P t).
Proof. exact (MK_COMB (@lem1121503 _26340) (@lem1121502 _26340 Q P t)). Qed.
Lemma lem1121505 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121506 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (t : list _26340) : (term155 _26340 Q P t) = (term148 _26340 Q P t).
Proof. exact (MK_COMB (@lem1121505) (@lem1121504 _26340 Q P t)). Qed.
Lemma lem1121507 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (@List.Forall _26340 Q t) = (@List.Forall _26340 Q t).
Proof. exact (eq_refl (@List.Forall _26340 Q t)). Qed.
Lemma lem1121508 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term150 _26340 P Q t) = (term149 _26340 P Q t).
Proof. exact (MK_COMB (@lem1121506 _26340 Q P t) (@lem1121507 _26340 Q t)). Qed.
Lemma lem1121509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1121510 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term156 _26340 P Q t) = (term157 _26340 P Q t).
Proof. exact (MK_COMB (@lem1121509) (@lem1121508 _26340 P Q t)). Qed.
Lemma lem1121511 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) (P : _26340 -> Prop) (t : list _26340) : (term152 _26340 Q P t x) = (term144 _26340 Q x P t).
Proof. exact (eq_refl (term152 _26340 Q P t x)). Qed.
Lemma lem1121512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121513 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) (P : _26340 -> Prop) (t : list _26340) : (term158 _26340 Q P t x) = (term159 _26340 Q x P t).
Proof. exact (MK_COMB (@lem1121512) (@lem1121511 _26340 Q x P t)). Qed.
Lemma lem1121514 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (@List.Forall _26340 Q t) = (@List.Forall _26340 Q t).
Proof. exact (eq_refl (@List.Forall _26340 Q t)). Qed.
Lemma lem1121515 {_26340 : Type'} (x : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term160 _26340 P x Q t) = (term161 _26340 x P Q t).
Proof. exact (MK_COMB (@lem1121513 _26340 Q x P t) (@lem1121514 _26340 Q t)). Qed.
Lemma lem1121516 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term162 _26340 P Q t) = (term163 _26340 P Q t).
Proof. exact (fun_ext (fun x : _26340 => @lem1121515 _26340 x P Q t)). Qed.
Lemma lem1121517 {_26340 : Type'} : (@ex _26340) = (@ex _26340).
Proof. exact (eq_refl (@ex _26340)). Qed.
Lemma lem1121518 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term151 _26340 P Q t) = (term164 _26340 P Q t).
Proof. exact (MK_COMB (@lem1121517 _26340) (@lem1121516 _26340 P Q t)). Qed.
Lemma lem1121519 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : ((term150 _26340 P Q t) = (term151 _26340 P Q t)) = ((term149 _26340 P Q t) = (term164 _26340 P Q t)).
Proof. exact (MK_COMB (@lem1121510 _26340 P Q t) (@lem1121518 _26340 P Q t)). Qed.
Lemma lem1121520 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term149 _26340 P Q t) = (term164 _26340 P Q t).
Proof. exact (EQ_MP (@lem1121519 _26340 P Q t) (@lem1121500 _26340 P Q t)). Qed.
Lemma lem1121522 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term130 _26340 P Q t) = (term164 _26340 P Q t).
Proof. exact (TRANS (@lem1121496 _26340 P Q t) (@lem1121520 _26340 P Q t)). Qed.
Lemma lem1121523 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term15 _26340 P Q t) = (term164 _26340 P Q t).
Proof. exact (TRANS (@lem1121419 _26340 P Q t) (@lem1121522 _26340 P Q t)). Qed.
Lemma lem1121524 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term15 _26340 P Q t) : term164 _26340 P Q t.
Proof. exact (EQ_MP (@lem1121523 _26340 P Q t) (@lem1121380 _26340 P Q t h1)). Qed.
Lemma lem1121531 {_26340 : Type'} (h : _26340) (x : _26340) (t : list _26340) : (term165 _26340 h x t) = (term166 _26340 h x t).
Proof. exact (@lem17160 (x = h) (@List.In _26340 x t)). Qed.
Lemma lem1121532 {_26340 : Type'} (P : _26340 -> Prop) (x : _26340) : (term167 _26340 P x) = (term167 _26340 P x).
Proof. exact (eq_refl (term167 _26340 P x)). Qed.
Lemma lem1121533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121534 {_26340 : Type'} (h : _26340) (x : _26340) (t : list _26340) : (term168 _26340 h x t) = (term169 _26340 h x t).
Proof. exact (MK_COMB (@lem1121533) (@lem1121531 _26340 h x t)). Qed.
Lemma lem1121535 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term170 _26340 h t P x) = (term171 _26340 h t P x).
Proof. exact (MK_COMB (@lem1121534 _26340 h x t) (@lem1121532 _26340 P x)). Qed.
Lemma lem1121536 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term172 _26340 h t P x) = (term170 _26340 h t P x).
Proof. exact (@lem17045 (term53 _26340 h x t) (P x)). Qed.
Lemma lem1121537 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term172 _26340 h t P x) = (term171 _26340 h t P x).
Proof. exact (TRANS (@lem1121536 _26340 h t P x) (@lem1121535 _26340 h t P x)). Qed.
Lemma lem1121538 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) : (Q x) = (Q x).
Proof. exact (eq_refl (Q x)). Qed.
Lemma lem1121539 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121540 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term173 _26340 h t P x) = (term174 _26340 h t P x).
Proof. exact (MK_COMB (@lem1121539) (@lem1121537 _26340 h t P x)). Qed.
Lemma lem1121541 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term175 _26340 h t P Q x) = (term176 _26340 h t P Q x).
Proof. exact (MK_COMB (@lem1121540 _26340 h t P x) (@lem1121538 _26340 Q x)). Qed.
Lemma lem1121542 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term61 _26340 h t P Q x) = (term175 _26340 h t P Q x).
Proof. exact (@lem17265 (term57 _26340 h t P x) (Q x)). Qed.
Lemma lem1121543 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term61 _26340 h t P Q x) = (term176 _26340 h t P Q x).
Proof. exact (TRANS (@lem1121542 _26340 h t P Q x) (@lem1121541 _26340 h t P Q x)). Qed.
Lemma lem1121544 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term63 _26340 h t P Q) = (term177 _26340 h t P Q).
Proof. exact (fun_ext (fun x : _26340 => @lem1121543 _26340 h t P Q x)). Qed.
Lemma lem1121545 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1121546 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term65 _26340 h t P Q) = (term178 _26340 h t P Q).
Proof. exact (MK_COMB (@lem1121545 _26340) (@lem1121544 _26340 h t P Q)). Qed.
Lemma lem1121551 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (t : list _26340) : (term69 _26340 h P t) = (term69 _26340 h P t).
Proof. exact (eq_refl (term69 _26340 h P t)). Qed.
Lemma lem1121552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1121553 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term67 _26340 h t P Q) = (term179 _26340 h t P Q).
Proof. exact (MK_COMB (@lem1121552) (@lem1121546 _26340 h t P Q)). Qed.
Lemma lem1121590 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) : (term71 _26340 Q h P t) = (term180 _26340 Q h P t).
Proof. exact (MK_COMB (@lem1121553 _26340 h t P Q) (@lem1121551 _26340 h P t)). Qed.
Lemma lem1121591 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term180 _26340 Q h P t.
Proof. exact (EQ_MP (@lem1121590 _26340 Q h P t) (@lem1121381 _26340 Q h P t h1)). Qed.
Lemma lem1121602 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term108 _26340 h Q t) = (term181 _26340 h Q t).
Proof. exact (@lem17045 (Q h) (@List.Forall _26340 Q t)). Qed.
Lemma lem1121603 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (h1 : term108 _26340 h Q t) : term181 _26340 h Q t.
Proof. exact (EQ_MP (@lem1121602 _26340 h Q t) (@lem1121386 _26340 h Q t h1)). Qed.
Lemma lem1121604 {_26340 : Type'} (x : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term161 _26340 x P Q t) : term161 _26340 x P Q t.
Proof. exact (h1). Qed.
Lemma lem1121609 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) : (@List.Forall _26340 P t) = (@List.Forall _26340 P t).
Proof. exact (eq_refl (@List.Forall _26340 P t)). Qed.
Lemma lem1121614 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1121615 {_26340 : Type'} (f : _26340 -> Prop) (x : _26340) : (f x) = (@I (_26340 -> Prop) f x).
Proof. exact (@lem1121614 _26340 Prop f x). Qed.
Lemma lem1121617 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) : (P h) = (@I (_26340 -> Prop) P h).
Proof. exact (@lem1121615 _26340 P h). Qed.
Lemma lem1121618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1121619 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) : (term182 _26340 P h) = (term183 _26340 P h).
Proof. exact (MK_COMB (@lem1121618) (@lem1121617 _26340 P h)). Qed.
Lemma lem1121620 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (t : list _26340) : (term69 _26340 h P t) = (term184 _26340 h P t).
Proof. exact (MK_COMB (@lem1121619 _26340 P h) (@lem1121609 _26340 P t)). Qed.
Lemma lem1121625 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1121626 {_26340 : Type'} (f : _26340 -> Prop) (x : _26340) : (f x) = (@I (_26340 -> Prop) f x).
Proof. exact (@lem1121625 _26340 Prop f x). Qed.
Lemma lem1121628 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) : (Q x) = (@I (_26340 -> Prop) Q x).
Proof. exact (@lem1121626 _26340 Q x). Qed.
Lemma lem1121629 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1121634 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1121635 {_26340 : Type'} (f : _26340 -> Prop) (x : _26340) : (f x) = (@I (_26340 -> Prop) f x).
Proof. exact (@lem1121634 _26340 Prop f x). Qed.
Lemma lem1121637 {_26340 : Type'} (P : _26340 -> Prop) (x : _26340) : (P x) = (@I (_26340 -> Prop) P x).
Proof. exact (@lem1121635 _26340 P x). Qed.
Lemma lem1121638 {_26340 : Type'} (P : _26340 -> Prop) (x : _26340) : (term167 _26340 P x) = (term185 _26340 P x).
Proof. exact (MK_COMB (@lem1121629) (@lem1121637 _26340 P x)). Qed.
Lemma lem1121657 {_26340 : Type'} (h : _26340) (x : _26340) (t : list _26340) : (term169 _26340 h x t) = (term169 _26340 h x t).
Proof. exact (eq_refl (term169 _26340 h x t)). Qed.
Lemma lem1121658 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term171 _26340 h t P x) = (term186 _26340 h t P x).
Proof. exact (MK_COMB (@lem1121657 _26340 h x t) (@lem1121638 _26340 P x)). Qed.
Lemma lem1121659 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121660 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term174 _26340 h t P x) = (term187 _26340 h t P x).
Proof. exact (MK_COMB (@lem1121659) (@lem1121658 _26340 h t P x)). Qed.
Lemma lem1121661 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term176 _26340 h t P Q x) = (term188 _26340 h t P Q x).
Proof. exact (MK_COMB (@lem1121660 _26340 h t P x) (@lem1121628 _26340 Q x)). Qed.
Lemma lem1121662 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term177 _26340 h t P Q) = (term189 _26340 h t P Q).
Proof. exact (fun_ext (fun x : _26340 => @lem1121661 _26340 h t P Q x)). Qed.
Lemma lem1121663 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1121664 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term178 _26340 h t P Q) = (term190 _26340 h t P Q).
Proof. exact (MK_COMB (@lem1121663 _26340) (@lem1121662 _26340 h t P Q)). Qed.
Lemma lem1121665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1121666 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term179 _26340 h t P Q) = (term191 _26340 h t P Q).
Proof. exact (MK_COMB (@lem1121665) (@lem1121664 _26340 h t P Q)). Qed.
Lemma lem1121667 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) : (term180 _26340 Q h P t) = (term192 _26340 Q h P t).
Proof. exact (MK_COMB (@lem1121666 _26340 h t P Q) (@lem1121620 _26340 h P t)). Qed.
Lemma lem1121668 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term192 _26340 Q h P t.
Proof. exact (EQ_MP (@lem1121667 _26340 Q h P t) (@lem1121591 _26340 Q h P t h1)). Qed.
Lemma lem1121675 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (term121 _26340 Q t) = (term121 _26340 Q t).
Proof. exact (eq_refl (term121 _26340 Q t)). Qed.
Lemma lem1121676 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1121681 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1121682 {_26340 : Type'} (f : _26340 -> Prop) (x : _26340) : (f x) = (@I (_26340 -> Prop) f x).
Proof. exact (@lem1121681 _26340 Prop f x). Qed.
Lemma lem1121684 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) : (Q h) = (@I (_26340 -> Prop) Q h).
Proof. exact (@lem1121682 _26340 Q h). Qed.
Lemma lem1121685 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) : (term167 _26340 Q h) = (term185 _26340 Q h).
Proof. exact (MK_COMB (@lem1121676) (@lem1121684 _26340 Q h)). Qed.
Lemma lem1121686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121687 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) : (term193 _26340 Q h) = (term194 _26340 Q h).
Proof. exact (MK_COMB (@lem1121686) (@lem1121685 _26340 Q h)). Qed.
Lemma lem1121688 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term181 _26340 h Q t) = (term195 _26340 h Q t).
Proof. exact (MK_COMB (@lem1121687 _26340 Q h) (@lem1121675 _26340 Q t)). Qed.
Lemma lem1121689 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (h1 : term108 _26340 h Q t) : term195 _26340 h Q t.
Proof. exact (EQ_MP (@lem1121688 _26340 h Q t) (@lem1121603 _26340 h Q t h1)). Qed.
Lemma lem1121694 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (@List.Forall _26340 Q t) = (@List.Forall _26340 Q t).
Proof. exact (eq_refl (@List.Forall _26340 Q t)). Qed.
Lemma lem1121701 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) : (term121 _26340 P t) = (term121 _26340 P t).
Proof. exact (eq_refl (term121 _26340 P t)). Qed.
Lemma lem1121702 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1121707 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1121708 {_26340 : Type'} (f : _26340 -> Prop) (x : _26340) : (f x) = (@I (_26340 -> Prop) f x).
Proof. exact (@lem1121707 _26340 Prop f x). Qed.
Lemma lem1121710 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) : (Q x) = (@I (_26340 -> Prop) Q x).
Proof. exact (@lem1121708 _26340 Q x). Qed.
Lemma lem1121711 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) : (term167 _26340 Q x) = (term185 _26340 Q x).
Proof. exact (MK_COMB (@lem1121702) (@lem1121710 _26340 Q x)). Qed.
Lemma lem1121716 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1121717 {_26340 : Type'} (f : _26340 -> Prop) (x : _26340) : (f x) = (@I (_26340 -> Prop) f x).
Proof. exact (@lem1121716 _26340 Prop f x). Qed.
Lemma lem1121719 {_26340 : Type'} (P : _26340 -> Prop) (x : _26340) : (P x) = (@I (_26340 -> Prop) P x).
Proof. exact (@lem1121717 _26340 P x). Qed.
Lemma lem1121726 {_26340 : Type'} (x : _26340) (t : list _26340) : (term196 _26340 x t) = (term196 _26340 x t).
Proof. exact (eq_refl (term196 _26340 x t)). Qed.
Lemma lem1121727 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term111 _26340 t P x) = (term197 _26340 t P x).
Proof. exact (MK_COMB (@lem1121726 _26340 x t) (@lem1121719 _26340 P x)). Qed.
Lemma lem1121728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1121729 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term198 _26340 t P x) = (term199 _26340 t P x).
Proof. exact (MK_COMB (@lem1121728) (@lem1121727 _26340 t P x)). Qed.
Lemma lem1121730 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term110 _26340 t P Q x) = (term200 _26340 t P Q x).
Proof. exact (MK_COMB (@lem1121729 _26340 t P x) (@lem1121711 _26340 Q x)). Qed.
Lemma lem1121731 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121732 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term142 _26340 t P Q x) = (term201 _26340 t P Q x).
Proof. exact (MK_COMB (@lem1121731) (@lem1121730 _26340 t P Q x)). Qed.
Lemma lem1121733 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) (P : _26340 -> Prop) (t : list _26340) : (term144 _26340 Q x P t) = (term202 _26340 Q x P t).
Proof. exact (MK_COMB (@lem1121732 _26340 t P Q x) (@lem1121701 _26340 P t)). Qed.
Lemma lem1121734 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121735 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) (P : _26340 -> Prop) (t : list _26340) : (term159 _26340 Q x P t) = (term203 _26340 Q x P t).
Proof. exact (MK_COMB (@lem1121734) (@lem1121733 _26340 Q x P t)). Qed.
Lemma lem1121736 {_26340 : Type'} (x : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) : (term161 _26340 x P Q t) = (term204 _26340 x P Q t).
Proof. exact (MK_COMB (@lem1121735 _26340 Q x P t) (@lem1121694 _26340 Q t)). Qed.
Lemma lem1121737 {_26340 : Type'} (x : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term161 _26340 x P Q t) : term204 _26340 x P Q t.
Proof. exact (EQ_MP (@lem1121736 _26340 x P Q t) (@lem1121604 _26340 x P Q t h1)). Qed.
Lemma lem1121738 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term184 _26340 h P t.
Proof. exact (proj2 (@lem1121668 _26340 Q h P t h1)). Qed.
Lemma lem1121739 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term190 _26340 h t P Q.
Proof. exact (proj1 (@lem1121668 _26340 Q h P t h1)). Qed.
Lemma lem1121742 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term202 _26340 Q x P t) : term202 _26340 Q x P t.
Proof. exact (h1). Qed.
Lemma lem1121744 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term200 _26340 t P Q x) : term200 _26340 t P Q x.
Proof. exact (h1). Qed.
Lemma lem1121747 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term200 _26340 t P Q x) : term197 _26340 t P x.
Proof. exact (proj1 (@lem1121744 _26340 t P Q x h1)). Qed.
Lemma lem1121757 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) : (@I (_26340 -> Prop) Q x) = (@I (_26340 -> Prop) Q x).
Proof. exact (eq_refl (@I (_26340 -> Prop) Q x)). Qed.
Lemma lem1121774 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term186 _26340 h t P x) = (term205 _26340 h t P x).
Proof. exact (@lem19699 (term206 _26340 x h) (term207 _26340 x t) (term185 _26340 P x)). Qed.
Lemma lem1121775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121776 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term187 _26340 h t P x) = (term208 _26340 h t P x).
Proof. exact (MK_COMB (@lem1121775) (@lem1121774 _26340 h t P x)). Qed.
Lemma lem1121777 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term188 _26340 h t P Q x) = (term209 _26340 h t P Q x).
Proof. exact (MK_COMB (@lem1121776 _26340 h t P x) (@lem1121757 _26340 Q x)). Qed.
Lemma lem1121784 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term209 _26340 h t P Q x) = (term210 _26340 h t P Q x).
Proof. exact (@lem19699 (term211 _26340 h P x) (term212 _26340 t P x) (@I (_26340 -> Prop) Q x)). Qed.
Lemma lem1121785 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term188 _26340 h t P Q x) = (term210 _26340 h t P Q x).
Proof. exact (TRANS (@lem1121777 _26340 h t P Q x) (@lem1121784 _26340 h t P Q x)). Qed.
Lemma lem1121786 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term189 _26340 h t P Q) = (term213 _26340 h t P Q).
Proof. exact (fun_ext (fun x : _26340 => @lem1121785 _26340 h t P Q x)). Qed.
Lemma lem1121787 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1121789 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term190 _26340 h t P Q) = (term214 _26340 h t P Q).
Proof. exact (MK_COMB (@lem1121787 _26340) (@lem1121786 _26340 h t P Q)). Qed.
Lemma lem1121790 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term214 _26340 h t P Q.
Proof. exact (EQ_MP (@lem1121789 _26340 h t P Q) (@lem1121739 _26340 Q h P t h1)). Qed.
Lemma lem1121814 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (h1 : term185 _26340 Q h) : term185 _26340 Q h.
Proof. exact (h1). Qed.
Lemma lem1121816 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) : (@I (_26340 -> Prop) Q x) = (@I (_26340 -> Prop) Q x).
Proof. exact (eq_refl (@I (_26340 -> Prop) Q x)). Qed.
Lemma lem1121833 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term186 _26340 h t P x) = (term205 _26340 h t P x).
Proof. exact (@lem19699 (term206 _26340 x h) (term207 _26340 x t) (term185 _26340 P x)). Qed.
Lemma lem1121834 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121835 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term187 _26340 h t P x) = (term208 _26340 h t P x).
Proof. exact (MK_COMB (@lem1121834) (@lem1121833 _26340 h t P x)). Qed.
Lemma lem1121836 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term188 _26340 h t P Q x) = (term209 _26340 h t P Q x).
Proof. exact (MK_COMB (@lem1121835 _26340 h t P x) (@lem1121816 _26340 Q x)). Qed.
Lemma lem1121843 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term209 _26340 h t P Q x) = (term210 _26340 h t P Q x).
Proof. exact (@lem19699 (term211 _26340 h P x) (term212 _26340 t P x) (@I (_26340 -> Prop) Q x)). Qed.
Lemma lem1121844 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term188 _26340 h t P Q x) = (term210 _26340 h t P Q x).
Proof. exact (TRANS (@lem1121836 _26340 h t P Q x) (@lem1121843 _26340 h t P Q x)). Qed.
Lemma lem1121845 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term189 _26340 h t P Q) = (term213 _26340 h t P Q).
Proof. exact (fun_ext (fun x : _26340 => @lem1121844 _26340 h t P Q x)). Qed.
Lemma lem1121846 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1121848 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term190 _26340 h t P Q) = (term214 _26340 h t P Q).
Proof. exact (MK_COMB (@lem1121846 _26340) (@lem1121845 _26340 h t P Q)). Qed.
Lemma lem1121849 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term214 _26340 h t P Q.
Proof. exact (EQ_MP (@lem1121848 _26340 h t P Q) (@lem1121739 _26340 Q h P t h1)). Qed.
Lemma lem1121920 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) : term121 _26340 P t.
Proof. exact (h1). Qed.
Lemma lem1121971 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) : term121 _26340 P t.
Proof. exact (h1). Qed.
Lemma lem1121977 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) : (@I (_26340 -> Prop) Q x) = (@I (_26340 -> Prop) Q x).
Proof. exact (eq_refl (@I (_26340 -> Prop) Q x)). Qed.
Lemma lem1121994 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term186 _26340 h t P x) = (term205 _26340 h t P x).
Proof. exact (@lem19699 (term206 _26340 x h) (term207 _26340 x t) (term185 _26340 P x)). Qed.
Lemma lem1121995 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1121996 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (x : _26340) : (term187 _26340 h t P x) = (term208 _26340 h t P x).
Proof. exact (MK_COMB (@lem1121995) (@lem1121994 _26340 h t P x)). Qed.
Lemma lem1121997 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term188 _26340 h t P Q x) = (term209 _26340 h t P Q x).
Proof. exact (MK_COMB (@lem1121996 _26340 h t P x) (@lem1121977 _26340 Q x)). Qed.
Lemma lem1122004 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term209 _26340 h t P Q x) = (term210 _26340 h t P Q x).
Proof. exact (@lem19699 (term211 _26340 h P x) (term212 _26340 t P x) (@I (_26340 -> Prop) Q x)). Qed.
Lemma lem1122005 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term188 _26340 h t P Q x) = (term210 _26340 h t P Q x).
Proof. exact (TRANS (@lem1121997 _26340 h t P Q x) (@lem1122004 _26340 h t P Q x)). Qed.
Lemma lem1122006 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term189 _26340 h t P Q) = (term213 _26340 h t P Q).
Proof. exact (fun_ext (fun x : _26340 => @lem1122005 _26340 h t P Q x)). Qed.
Lemma lem1122007 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1122009 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term190 _26340 h t P Q) = (term214 _26340 h t P Q).
Proof. exact (MK_COMB (@lem1122007 _26340) (@lem1122006 _26340 h t P Q)). Qed.
Lemma lem1122010 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term214 _26340 h t P Q.
Proof. exact (EQ_MP (@lem1122009 _26340 h t P Q) (@lem1121739 _26340 Q h P t h1)). Qed.
Lemma lem1122026 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (h1 : term185 _26340 Q h) : term185 _26340 Q h.
Proof. exact (h1). Qed.
Lemma lem1122073 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : @List.Forall _26340 Q t) : @List.Forall _26340 Q t.
Proof. exact (h1). Qed.
Lemma lem1122077 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) : term121 _26340 Q t.
Proof. exact (h1). Qed.
Lemma lem1122078 {_26340 : Type'} (_18264 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term215 _26340 h t P Q _18264.
Proof. exact (@lem1121790 _26340 Q h P t h1 _18264). Qed.
Lemma lem1122079 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18264 : _26340) : (term215 _26340 h t P Q _18264) = (term210 _26340 h t P Q _18264).
Proof. exact (eq_refl (term215 _26340 h t P Q _18264)). Qed.
Lemma lem1122080 {_26340 : Type'} (_18264 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term210 _26340 h t P Q _18264.
Proof. exact (EQ_MP (@lem1122079 _26340 h t P Q _18264) (@lem1122078 _26340 _18264 Q h P t h1)). Qed.
Lemma lem1122081 {_26340 : Type'} (_18265 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term215 _26340 h t P Q _18265.
Proof. exact (@lem1121849 _26340 Q h P t h1 _18265). Qed.
Lemma lem1122082 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18265 : _26340) : (term215 _26340 h t P Q _18265) = (term210 _26340 h t P Q _18265).
Proof. exact (eq_refl (term215 _26340 h t P Q _18265)). Qed.
Lemma lem1122083 {_26340 : Type'} (_18265 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term210 _26340 h t P Q _18265.
Proof. exact (EQ_MP (@lem1122082 _26340 h t P Q _18265) (@lem1122081 _26340 _18265 Q h P t h1)). Qed.
Lemma lem1122090 {_26340 : Type'} (_18268 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term215 _26340 h t P Q _18268.
Proof. exact (@lem1122010 _26340 Q h P t h1 _18268). Qed.
Lemma lem1122091 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18268 : _26340) : (term215 _26340 h t P Q _18268) = (term210 _26340 h t P Q _18268).
Proof. exact (eq_refl (term215 _26340 h t P Q _18268)). Qed.
Lemma lem1122092 {_26340 : Type'} (_18268 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term210 _26340 h t P Q _18268.
Proof. exact (EQ_MP (@lem1122091 _26340 h t P Q _18268) (@lem1122090 _26340 _18268 Q h P t h1)). Qed.
Lemma lem1122097 {_26340 : Type'} (_18264 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term216 _26340 h P Q _18264.
Proof. exact (proj1 (@lem1122080 _26340 _18264 Q h P t h1)). Qed.
Lemma lem1122098 {_26340 : Type'} (_18265 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term217 _26340 t P Q _18265.
Proof. exact (proj2 (@lem1122083 _26340 _18265 Q h P t h1)). Qed.
Lemma lem1122105 {_26340 : Type'} (_18268 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term216 _26340 h P Q _18268.
Proof. exact (proj1 (@lem1122092 _26340 _18268 Q h P t h1)). Qed.
Lemma lem1122119 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (h1 : term185 _26340 Q h) : term185 _26340 Q h.
Proof. exact (h1). Qed.
Lemma lem1122130 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18264 : _26340) : (term216 _26340 h P Q _18264) = (term218 _26340 h P Q _18264).
Proof. exact (@lem1120982 (term206 _26340 _18264 h) (term185 _26340 P _18264) (@I (_26340 -> Prop) Q _18264)). Qed.
Lemma lem1122131 {_26340 : Type'} (_18264 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term218 _26340 h P Q _18264.
Proof. exact (EQ_MP (@lem1122130 _26340 h P Q _18264) (@lem1122097 _26340 _18264 Q h P t h1)). Qed.
Lemma lem1122149 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term200 _26340 t P Q x) : term185 _26340 Q x.
Proof. exact (proj2 (@lem1121744 _26340 t P Q x h1)). Qed.
Lemma lem1122178 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18265 : _26340) : (term217 _26340 t P Q _18265) = (term219 _26340 t P Q _18265).
Proof. exact (@lem1120982 (term207 _26340 _18265 t) (term185 _26340 P _18265) (@I (_26340 -> Prop) Q _18265)). Qed.
Lemma lem1122179 {_26340 : Type'} (_18265 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term219 _26340 t P Q _18265.
Proof. exact (EQ_MP (@lem1122178 _26340 t P Q _18265) (@lem1122098 _26340 _18265 Q h P t h1)). Qed.
Lemma lem1122185 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) : term121 _26340 P t.
Proof. exact (h1). Qed.
Lemma lem1122217 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) : term121 _26340 P t.
Proof. exact (h1). Qed.
Lemma lem1122251 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (h1 : term185 _26340 Q h) : term185 _26340 Q h.
Proof. exact (h1). Qed.
Lemma lem1122262 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18268 : _26340) : (term216 _26340 h P Q _18268) = (term218 _26340 h P Q _18268).
Proof. exact (@lem1120982 (term206 _26340 _18268 h) (term185 _26340 P _18268) (@I (_26340 -> Prop) Q _18268)). Qed.
Lemma lem1122263 {_26340 : Type'} (_18268 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term218 _26340 h P Q _18268.
Proof. exact (EQ_MP (@lem1122262 _26340 h P Q _18268) (@lem1122105 _26340 _18268 Q h P t h1)). Qed.
Lemma lem1122281 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : @List.Forall _26340 Q t) : @List.Forall _26340 Q t.
Proof. exact (h1). Qed.
Lemma lem1122283 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) : term121 _26340 Q t.
Proof. exact (h1). Qed.
Lemma lem1122372 {_26340 : Type'} (x : _26340) : x = x.
Proof. exact (@lem21386 _26340 x). Qed.
Lemma lem1122373 {_26340 : Type'} (x : _26340) : x = x.
Proof. exact (@lem1122372 _26340 x). Qed.
Lemma lem1122374 {_26340 : Type'} (h : _26340) : h = h.
Proof. exact (@lem1122373 _26340 h). Qed.
Lemma lem1122375 {_26340 : Type'} (h : _26340) : term220 _26340 h.
Proof. exact (fun h0 : term221 _26340 h => @lem1122374 _26340 h). Qed.
Lemma lem1122377 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122378 {_26340 : Type'} (h : _26340) : (term220 _26340 h) = (h = h).
Proof. exact (@lem1122377 (h = h)). Qed.
Lemma lem1122379 {_26340 : Type'} (h : _26340) : h = h.
Proof. exact (EQ_MP (@lem1122378 _26340 h) (@lem1122375 _26340 h)). Qed.
Lemma lem1122381 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : @I (_26340 -> Prop) P h.
Proof. exact (proj1 (@lem1121738 _26340 Q h P t h1)). Qed.
Lemma lem1122382 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term223 _26340 P h.
Proof. exact (fun h0 : term185 _26340 P h => @lem1122381 _26340 Q h P t h1). Qed.
Lemma lem1122384 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122385 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) : (term223 _26340 P h) = (@I (_26340 -> Prop) P h).
Proof. exact (@lem1122384 (@I (_26340 -> Prop) P h)). Qed.
Lemma lem1122386 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : @I (_26340 -> Prop) P h.
Proof. exact (EQ_MP (@lem1122385 _26340 P h) (@lem1122382 _26340 Q h P t h1)). Qed.
Lemma lem1122404 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1122405 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (_18264 : _26340) : (term224 _26340 P Q _18264) = (term225 _26340 Q P _18264).
Proof. exact (@lem1122404 (@I (_26340 -> Prop) Q _18264) (term185 _26340 P _18264)). Qed.
Lemma lem1122411 {_26340 : Type'} (_18264 : _26340) (h : _26340) : (term226 _26340 _18264 h) = (term226 _26340 _18264 h).
Proof. exact (eq_refl (term226 _26340 _18264 h)). Qed.
Lemma lem1122412 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (P : _26340 -> Prop) (_18264 : _26340) : (term218 _26340 h P Q _18264) = (term227 _26340 h Q P _18264).
Proof. exact (MK_COMB (@lem1122411 _26340 _18264 h) (@lem1122405 _26340 Q P _18264)). Qed.
Lemma lem1122416 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1122417 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : (term227 _26340 h Q P _18264) = (term228 _26340 Q h P _18264).
Proof. exact (@lem1122416 (@I (_26340 -> Prop) Q _18264) (term206 _26340 _18264 h) (term185 _26340 P _18264)). Qed.
Lemma lem1122435 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : (term218 _26340 h P Q _18264) = (term228 _26340 Q h P _18264).
Proof. exact (TRANS (@lem1122412 _26340 h Q P _18264) (@lem1122417 _26340 Q h P _18264)). Qed.
Lemma lem1122436 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1122437 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : (term229 _26340 h P Q _18264) = (term230 _26340 Q h P _18264).
Proof. exact (MK_COMB (@lem1122436) (@lem1122435 _26340 Q h P _18264)). Qed.
Lemma lem1122455 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : (term228 _26340 Q h P _18264) = (term228 _26340 Q h P _18264).
Proof. exact (eq_refl (term228 _26340 Q h P _18264)). Qed.
Lemma lem1122456 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : ((term218 _26340 h P Q _18264) = (term228 _26340 Q h P _18264)) = ((term228 _26340 Q h P _18264) = (term228 _26340 Q h P _18264)).
Proof. exact (MK_COMB (@lem1122437 _26340 Q h P _18264) (@lem1122455 _26340 Q h P _18264)). Qed.
Lemma lem1122458 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1122459 (x : Prop) : (x = x) = True.
Proof. exact (@lem1122458 Prop x). Qed.
Lemma lem1122460 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : ((term228 _26340 Q h P _18264) = (term228 _26340 Q h P _18264)) = True.
Proof. exact (@lem1122459 (term228 _26340 Q h P _18264)). Qed.
Lemma lem1122461 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : ((term218 _26340 h P Q _18264) = (term228 _26340 Q h P _18264)) = True.
Proof. exact (TRANS (@lem1122456 _26340 Q h P _18264) (@lem1122460 _26340 Q h P _18264)). Qed.
Lemma lem1122462 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : True = ((term218 _26340 h P Q _18264) = (term228 _26340 Q h P _18264)).
Proof. exact (SYM (@lem1122461 _26340 Q h P _18264)). Qed.
Lemma lem1122463 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : (term218 _26340 h P Q _18264) = (term228 _26340 Q h P _18264).
Proof. exact (EQ_MP (@lem1122462 _26340 Q h P _18264) (@lem0)). Qed.
Lemma lem1122464 {_26340 : Type'} (_18264 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term228 _26340 Q h P _18264.
Proof. exact (EQ_MP (@lem1122463 _26340 Q h P _18264) (@lem1122131 _26340 _18264 Q h P t h1)). Qed.
Lemma lem1122466 (b : Prop) (a : Prop) : (a \/ b) = (term231 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1122467 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18264 : _26340) : (term228 _26340 Q h P _18264) = (term232 _26340 h P Q _18264).
Proof. exact (@lem1122466 (term211 _26340 h P _18264) (@I (_26340 -> Prop) Q _18264)). Qed.
Lemma lem1122469 (a : Prop) (b : Prop) : (term233 a b) = (term234 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1122470 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : (term235 _26340 h P _18264) = (term236 _26340 h P _18264).
Proof. exact (@lem1122469 (term206 _26340 _18264 h) (term185 _26340 P _18264)). Qed.
Lemma lem1122472 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1122473 {_26340 : Type'} (_18264 : _26340) (h : _26340) : (term237 _26340 _18264 h) = (_18264 = h).
Proof. exact (@lem1122472 (_18264 = h)). Qed.
Lemma lem1122474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1122475 {_26340 : Type'} (_18264 : _26340) (h : _26340) : (term238 _26340 _18264 h) = (term239 _26340 _18264 h).
Proof. exact (MK_COMB (@lem1122474) (@lem1122473 _26340 _18264 h)). Qed.
Lemma lem1122477 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1122478 {_26340 : Type'} (P : _26340 -> Prop) (_18264 : _26340) : (term240 _26340 P _18264) = (@I (_26340 -> Prop) P _18264).
Proof. exact (@lem1122477 (@I (_26340 -> Prop) P _18264)). Qed.
Lemma lem1122479 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : (term236 _26340 h P _18264) = (term241 _26340 h P _18264).
Proof. exact (MK_COMB (@lem1122475 _26340 _18264 h) (@lem1122478 _26340 P _18264)). Qed.
Lemma lem1122480 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : (term235 _26340 h P _18264) = (term241 _26340 h P _18264).
Proof. exact (TRANS (@lem1122470 _26340 h P _18264) (@lem1122479 _26340 h P _18264)). Qed.
Lemma lem1122481 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1122482 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (_18264 : _26340) : (term242 _26340 h P _18264) = (term243 _26340 h P _18264).
Proof. exact (MK_COMB (@lem1122481) (@lem1122480 _26340 h P _18264)). Qed.
Lemma lem1122483 {_26340 : Type'} (Q : _26340 -> Prop) (_18264 : _26340) : (@I (_26340 -> Prop) Q _18264) = (@I (_26340 -> Prop) Q _18264).
Proof. exact (eq_refl (@I (_26340 -> Prop) Q _18264)). Qed.
Lemma lem1122484 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18264 : _26340) : (term232 _26340 h P Q _18264) = (term244 _26340 h P Q _18264).
Proof. exact (MK_COMB (@lem1122482 _26340 h P _18264) (@lem1122483 _26340 Q _18264)). Qed.
Lemma lem1122485 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18264 : _26340) : (term228 _26340 Q h P _18264) = (term244 _26340 h P Q _18264).
Proof. exact (TRANS (@lem1122467 _26340 h P Q _18264) (@lem1122484 _26340 h P Q _18264)). Qed.
Lemma lem1122487 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term245 _26340 P h.
Proof. exact (conj (@lem1122379 _26340 h) (@lem1122386 _26340 Q h P t h1)). Qed.
Lemma lem1122489 {_26340 : Type'} (_18264 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term244 _26340 h P Q _18264.
Proof. exact (EQ_MP (@lem1122485 _26340 h P Q _18264) (@lem1122464 _26340 _18264 Q h P t h1)). Qed.
Lemma lem1122490 {_26340 : Type'} (_18264 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term244 _26340 h P Q _18264.
Proof. exact (@lem1122489 _26340 _18264 Q h P t h1). Qed.
Lemma lem1122491 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term246 _26340 P Q h.
Proof. exact (@lem1122490 _26340 h Q h P t h1). Qed.
Lemma lem1122494 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : @I (_26340 -> Prop) Q h.
Proof. exact (@lem1122491 _26340 Q h P t h1 (@lem1122487 _26340 Q h P t h1)). Qed.
Lemma lem1122495 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term223 _26340 Q h.
Proof. exact (fun h0 : term185 _26340 Q h => @lem1122494 _26340 Q h P t h1). Qed.
Lemma lem1122497 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122498 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) : (term223 _26340 Q h) = (@I (_26340 -> Prop) Q h).
Proof. exact (@lem1122497 (@I (_26340 -> Prop) Q h)). Qed.
Lemma lem1122499 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : @I (_26340 -> Prop) Q h.
Proof. exact (EQ_MP (@lem1122498 _26340 Q h) (@lem1122495 _26340 Q h P t h1)). Qed.
Lemma lem1122502 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1122504 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) : (term185 _26340 Q h) = (term247 _26340 Q h).
Proof. exact (@lem1122502 (@I (_26340 -> Prop) Q h)). Qed.
Lemma lem1122507 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (h1 : term185 _26340 Q h) : term247 _26340 Q h.
Proof. exact (EQ_MP (@lem1122504 _26340 Q h) (@lem1122119 _26340 Q h h1)). Qed.
Lemma lem1122510 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (@lem1122507 _26340 Q h h1 (@lem1122499 _26340 Q h P t h2)). Qed.
Lemma lem1122511 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : term248.
Proof. exact (fun h0 : ~ False => @lem1122510 _26340 Q h P t h1 h2). Qed.
Lemma lem1122513 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122514 : term248 = False.
Proof. exact (@lem1122513 False). Qed.
Lemma lem1122515 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1122514) (@lem1122511 _26340 Q h P t h1 h2)). Qed.
Lemma lem1122580 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term200 _26340 t P Q x) : @List.In _26340 x t.
Proof. exact (proj1 (@lem1121747 _26340 t P Q x h1)). Qed.
Lemma lem1122581 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term200 _26340 t P Q x) : term249 _26340 x t.
Proof. exact (fun h0 : term207 _26340 x t => @lem1122580 _26340 t P Q x h1). Qed.
Lemma lem1122583 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122584 {_26340 : Type'} (x : _26340) (t : list _26340) : (term249 _26340 x t) = (@List.In _26340 x t).
Proof. exact (@lem1122583 (@List.In _26340 x t)). Qed.
Lemma lem1122585 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term200 _26340 t P Q x) : @List.In _26340 x t.
Proof. exact (EQ_MP (@lem1122584 _26340 x t) (@lem1122581 _26340 t P Q x h1)). Qed.
Lemma lem1122587 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term200 _26340 t P Q x) : @I (_26340 -> Prop) P x.
Proof. exact (proj2 (@lem1121747 _26340 t P Q x h1)). Qed.
Lemma lem1122588 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term200 _26340 t P Q x) : term223 _26340 P x.
Proof. exact (fun h0 : term185 _26340 P x => @lem1122587 _26340 t P Q x h1). Qed.
Lemma lem1122590 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122591 {_26340 : Type'} (P : _26340 -> Prop) (x : _26340) : (term223 _26340 P x) = (@I (_26340 -> Prop) P x).
Proof. exact (@lem1122590 (@I (_26340 -> Prop) P x)). Qed.
Lemma lem1122592 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term200 _26340 t P Q x) : @I (_26340 -> Prop) P x.
Proof. exact (EQ_MP (@lem1122591 _26340 P x) (@lem1122588 _26340 t P Q x h1)). Qed.
Lemma lem1122598 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1122599 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) (Q : _26340 -> Prop) (_18265 : _26340) : (term219 _26340 t P Q _18265) = (term250 _26340 P t Q _18265).
Proof. exact (@lem1122598 (term185 _26340 P _18265) (term207 _26340 _18265 t) (@I (_26340 -> Prop) Q _18265)). Qed.
Lemma lem1122613 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1122614 {_26340 : Type'} (Q : _26340 -> Prop) (_18265 : _26340) (t : list _26340) : (term251 _26340 t Q _18265) = (term252 _26340 Q _18265 t).
Proof. exact (@lem1122613 (@I (_26340 -> Prop) Q _18265) (term207 _26340 _18265 t)). Qed.
Lemma lem1122620 {_26340 : Type'} (P : _26340 -> Prop) (_18265 : _26340) : (term194 _26340 P _18265) = (term194 _26340 P _18265).
Proof. exact (eq_refl (term194 _26340 P _18265)). Qed.
Lemma lem1122621 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18265 : _26340) (t : list _26340) : (term250 _26340 P t Q _18265) = (term253 _26340 P Q _18265 t).
Proof. exact (MK_COMB (@lem1122620 _26340 P _18265) (@lem1122614 _26340 Q _18265 t)). Qed.
Lemma lem1122625 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1122626 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (_18265 : _26340) (t : list _26340) : (term253 _26340 P Q _18265 t) = (term254 _26340 Q P _18265 t).
Proof. exact (@lem1122625 (@I (_26340 -> Prop) Q _18265) (term185 _26340 P _18265) (term207 _26340 _18265 t)). Qed.
Lemma lem1122642 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (_18265 : _26340) (t : list _26340) : (term250 _26340 P t Q _18265) = (term254 _26340 Q P _18265 t).
Proof. exact (TRANS (@lem1122621 _26340 P Q _18265 t) (@lem1122626 _26340 Q P _18265 t)). Qed.
Lemma lem1122643 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (_18265 : _26340) (t : list _26340) : (term219 _26340 t P Q _18265) = (term254 _26340 Q P _18265 t).
Proof. exact (TRANS (@lem1122599 _26340 P t Q _18265) (@lem1122642 _26340 Q P _18265 t)). Qed.
Lemma lem1122644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1122645 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (_18265 : _26340) (t : list _26340) : (term255 _26340 t P Q _18265) = (term256 _26340 Q P _18265 t).
Proof. exact (MK_COMB (@lem1122644) (@lem1122643 _26340 Q P _18265 t)). Qed.
Lemma lem1122659 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1122660 {_26340 : Type'} (P : _26340 -> Prop) (_18265 : _26340) (t : list _26340) : (term212 _26340 t P _18265) = (term257 _26340 P _18265 t).
Proof. exact (@lem1122659 (term185 _26340 P _18265) (term207 _26340 _18265 t)). Qed.
Lemma lem1122666 {_26340 : Type'} (Q : _26340 -> Prop) (_18265 : _26340) : (term258 _26340 Q _18265) = (term258 _26340 Q _18265).
Proof. exact (eq_refl (term258 _26340 Q _18265)). Qed.
Lemma lem1122667 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (_18265 : _26340) (t : list _26340) : (term259 _26340 Q t P _18265) = (term254 _26340 Q P _18265 t).
Proof. exact (MK_COMB (@lem1122666 _26340 Q _18265) (@lem1122660 _26340 P _18265 t)). Qed.
Lemma lem1122678 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (_18265 : _26340) (t : list _26340) : ((term219 _26340 t P Q _18265) = (term259 _26340 Q t P _18265)) = ((term254 _26340 Q P _18265 t) = (term254 _26340 Q P _18265 t)).
Proof. exact (MK_COMB (@lem1122645 _26340 Q P _18265 t) (@lem1122667 _26340 Q P _18265 t)). Qed.
Lemma lem1122680 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1122681 (x : Prop) : (x = x) = True.
Proof. exact (@lem1122680 Prop x). Qed.
Lemma lem1122682 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (_18265 : _26340) (t : list _26340) : ((term254 _26340 Q P _18265 t) = (term254 _26340 Q P _18265 t)) = True.
Proof. exact (@lem1122681 (term254 _26340 Q P _18265 t)). Qed.
Lemma lem1122683 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (P : _26340 -> Prop) (_18265 : _26340) : ((term219 _26340 t P Q _18265) = (term259 _26340 Q t P _18265)) = True.
Proof. exact (TRANS (@lem1122678 _26340 Q P _18265 t) (@lem1122682 _26340 Q P _18265 t)). Qed.
Lemma lem1122684 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (P : _26340 -> Prop) (_18265 : _26340) : True = ((term219 _26340 t P Q _18265) = (term259 _26340 Q t P _18265)).
Proof. exact (SYM (@lem1122683 _26340 Q t P _18265)). Qed.
Lemma lem1122685 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (P : _26340 -> Prop) (_18265 : _26340) : (term219 _26340 t P Q _18265) = (term259 _26340 Q t P _18265).
Proof. exact (EQ_MP (@lem1122684 _26340 Q t P _18265) (@lem0)). Qed.
Lemma lem1122686 {_26340 : Type'} (_18265 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term259 _26340 Q t P _18265.
Proof. exact (EQ_MP (@lem1122685 _26340 Q t P _18265) (@lem1122179 _26340 _18265 Q h P t h1)). Qed.
Lemma lem1122688 (b : Prop) (a : Prop) : (a \/ b) = (term231 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1122689 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18265 : _26340) : (term259 _26340 Q t P _18265) = (term260 _26340 t P Q _18265).
Proof. exact (@lem1122688 (term212 _26340 t P _18265) (@I (_26340 -> Prop) Q _18265)). Qed.
Lemma lem1122691 (a : Prop) (b : Prop) : (term233 a b) = (term234 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1122692 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (_18265 : _26340) : (term261 _26340 t P _18265) = (term262 _26340 t P _18265).
Proof. exact (@lem1122691 (term207 _26340 _18265 t) (term185 _26340 P _18265)). Qed.
Lemma lem1122694 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1122695 {_26340 : Type'} (_18265 : _26340) (t : list _26340) : (term263 _26340 _18265 t) = (@List.In _26340 _18265 t).
Proof. exact (@lem1122694 (@List.In _26340 _18265 t)). Qed.
Lemma lem1122696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1122697 {_26340 : Type'} (_18265 : _26340) (t : list _26340) : (term264 _26340 _18265 t) = (term196 _26340 _18265 t).
Proof. exact (MK_COMB (@lem1122696) (@lem1122695 _26340 _18265 t)). Qed.
Lemma lem1122699 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1122700 {_26340 : Type'} (P : _26340 -> Prop) (_18265 : _26340) : (term240 _26340 P _18265) = (@I (_26340 -> Prop) P _18265).
Proof. exact (@lem1122699 (@I (_26340 -> Prop) P _18265)). Qed.
Lemma lem1122701 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (_18265 : _26340) : (term262 _26340 t P _18265) = (term197 _26340 t P _18265).
Proof. exact (MK_COMB (@lem1122697 _26340 _18265 t) (@lem1122700 _26340 P _18265)). Qed.
Lemma lem1122702 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (_18265 : _26340) : (term261 _26340 t P _18265) = (term197 _26340 t P _18265).
Proof. exact (TRANS (@lem1122692 _26340 t P _18265) (@lem1122701 _26340 t P _18265)). Qed.
Lemma lem1122703 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1122704 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (_18265 : _26340) : (term265 _26340 t P _18265) = (term266 _26340 t P _18265).
Proof. exact (MK_COMB (@lem1122703) (@lem1122702 _26340 t P _18265)). Qed.
Lemma lem1122705 {_26340 : Type'} (Q : _26340 -> Prop) (_18265 : _26340) : (@I (_26340 -> Prop) Q _18265) = (@I (_26340 -> Prop) Q _18265).
Proof. exact (eq_refl (@I (_26340 -> Prop) Q _18265)). Qed.
Lemma lem1122706 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18265 : _26340) : (term260 _26340 t P Q _18265) = (term267 _26340 t P Q _18265).
Proof. exact (MK_COMB (@lem1122704 _26340 t P _18265) (@lem1122705 _26340 Q _18265)). Qed.
Lemma lem1122707 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18265 : _26340) : (term259 _26340 Q t P _18265) = (term267 _26340 t P Q _18265).
Proof. exact (TRANS (@lem1122689 _26340 t P Q _18265) (@lem1122706 _26340 t P Q _18265)). Qed.
Lemma lem1122709 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term200 _26340 t P Q x) : term197 _26340 t P x.
Proof. exact (conj (@lem1122585 _26340 t P Q x h1) (@lem1122592 _26340 t P Q x h1)). Qed.
Lemma lem1122711 {_26340 : Type'} (_18265 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term267 _26340 t P Q _18265.
Proof. exact (EQ_MP (@lem1122707 _26340 t P Q _18265) (@lem1122686 _26340 _18265 Q h P t h1)). Qed.
Lemma lem1122712 {_26340 : Type'} (_18265 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term267 _26340 t P Q _18265.
Proof. exact (@lem1122711 _26340 _18265 Q h P t h1). Qed.
Lemma lem1122713 {_26340 : Type'} (x : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term267 _26340 t P Q x.
Proof. exact (@lem1122712 _26340 x Q h P t h1). Qed.
Lemma lem1122716 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term71 _26340 Q h P t) (h2 : term200 _26340 t P Q x) : @I (_26340 -> Prop) Q x.
Proof. exact (@lem1122713 _26340 x Q h P t h1 (@lem1122709 _26340 t P Q x h2)). Qed.
Lemma lem1122717 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term71 _26340 Q h P t) (h2 : term200 _26340 t P Q x) : term223 _26340 Q x.
Proof. exact (fun h0 : term185 _26340 Q x => @lem1122716 _26340 h t P Q x h1 h2). Qed.
Lemma lem1122719 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122720 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) : (term223 _26340 Q x) = (@I (_26340 -> Prop) Q x).
Proof. exact (@lem1122719 (@I (_26340 -> Prop) Q x)). Qed.
Lemma lem1122721 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term71 _26340 Q h P t) (h2 : term200 _26340 t P Q x) : @I (_26340 -> Prop) Q x.
Proof. exact (EQ_MP (@lem1122720 _26340 Q x) (@lem1122717 _26340 h t P Q x h1 h2)). Qed.
Lemma lem1122724 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1122726 {_26340 : Type'} (Q : _26340 -> Prop) (x : _26340) : (term185 _26340 Q x) = (term247 _26340 Q x).
Proof. exact (@lem1122724 (@I (_26340 -> Prop) Q x)). Qed.
Lemma lem1122729 {_26340 : Type'} (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term200 _26340 t P Q x) : term247 _26340 Q x.
Proof. exact (EQ_MP (@lem1122726 _26340 Q x) (@lem1122149 _26340 t P Q x h1)). Qed.
Lemma lem1122732 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term71 _26340 Q h P t) (h2 : term200 _26340 t P Q x) : False.
Proof. exact (@lem1122729 _26340 t P Q x h2 (@lem1122721 _26340 h t P Q x h1 h2)). Qed.
Lemma lem1122733 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term71 _26340 Q h P t) (h2 : term200 _26340 t P Q x) : term248.
Proof. exact (fun h0 : ~ False => @lem1122732 _26340 h t P Q x h1 h2). Qed.
Lemma lem1122735 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122736 : term248 = False.
Proof. exact (@lem1122735 False). Qed.
Lemma lem1122737 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term71 _26340 Q h P t) (h2 : term200 _26340 t P Q x) : False.
Proof. exact (EQ_MP (@lem1122736) (@lem1122733 _26340 h t P Q x h1 h2)). Qed.
Lemma lem1122802 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : @List.Forall _26340 P t.
Proof. exact (proj2 (@lem1121738 _26340 Q h P t h1)). Qed.
Lemma lem1122803 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term268 _26340 P t.
Proof. exact (fun h0 : term121 _26340 P t => @lem1122802 _26340 Q h P t h1). Qed.
Lemma lem1122805 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122806 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) : (term268 _26340 P t) = (@List.Forall _26340 P t).
Proof. exact (@lem1122805 (@List.Forall _26340 P t)). Qed.
Lemma lem1122807 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : @List.Forall _26340 P t.
Proof. exact (EQ_MP (@lem1122806 _26340 P t) (@lem1122803 _26340 Q h P t h1)). Qed.
Lemma lem1122810 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1122812 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) : (term121 _26340 P t) = (term269 _26340 P t).
Proof. exact (@lem1122810 (@List.Forall _26340 P t)). Qed.
Lemma lem1122815 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) : term269 _26340 P t.
Proof. exact (EQ_MP (@lem1122812 _26340 P t) (@lem1122185 _26340 P t h1)). Qed.
Lemma lem1122818 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (@lem1122815 _26340 P t h1 (@lem1122807 _26340 Q h P t h2)). Qed.
Lemma lem1122819 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : term248.
Proof. exact (fun h0 : ~ False => @lem1122818 _26340 Q h P t h1 h2). Qed.
Lemma lem1122821 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122822 : term248 = False.
Proof. exact (@lem1122821 False). Qed.
Lemma lem1122823 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1122822) (@lem1122819 _26340 Q h P t h1 h2)). Qed.
Lemma lem1122888 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : @List.Forall _26340 P t.
Proof. exact (proj2 (@lem1121738 _26340 Q h P t h1)). Qed.
Lemma lem1122889 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term268 _26340 P t.
Proof. exact (fun h0 : term121 _26340 P t => @lem1122888 _26340 Q h P t h1). Qed.
Lemma lem1122891 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122892 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) : (term268 _26340 P t) = (@List.Forall _26340 P t).
Proof. exact (@lem1122891 (@List.Forall _26340 P t)). Qed.
Lemma lem1122893 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : @List.Forall _26340 P t.
Proof. exact (EQ_MP (@lem1122892 _26340 P t) (@lem1122889 _26340 Q h P t h1)). Qed.
Lemma lem1122896 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1122898 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) : (term121 _26340 P t) = (term269 _26340 P t).
Proof. exact (@lem1122896 (@List.Forall _26340 P t)). Qed.
Lemma lem1122901 {_26340 : Type'} (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) : term269 _26340 P t.
Proof. exact (EQ_MP (@lem1122898 _26340 P t) (@lem1122217 _26340 P t h1)). Qed.
Lemma lem1122904 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (@lem1122901 _26340 P t h1 (@lem1122893 _26340 Q h P t h2)). Qed.
Lemma lem1122905 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : term248.
Proof. exact (fun h0 : ~ False => @lem1122904 _26340 Q h P t h1 h2). Qed.
Lemma lem1122907 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122908 : term248 = False.
Proof. exact (@lem1122907 False). Qed.
Lemma lem1122909 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1122908) (@lem1122905 _26340 Q h P t h1 h2)). Qed.
Lemma lem1122974 {_26340 : Type'} (x : _26340) : x = x.
Proof. exact (@lem21386 _26340 x). Qed.
Lemma lem1122975 {_26340 : Type'} (x : _26340) : x = x.
Proof. exact (@lem1122974 _26340 x). Qed.
Lemma lem1122976 {_26340 : Type'} (h : _26340) : h = h.
Proof. exact (@lem1122975 _26340 h). Qed.
Lemma lem1122977 {_26340 : Type'} (h : _26340) : term220 _26340 h.
Proof. exact (fun h0 : term221 _26340 h => @lem1122976 _26340 h). Qed.
Lemma lem1122979 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122980 {_26340 : Type'} (h : _26340) : (term220 _26340 h) = (h = h).
Proof. exact (@lem1122979 (h = h)). Qed.
Lemma lem1122981 {_26340 : Type'} (h : _26340) : h = h.
Proof. exact (EQ_MP (@lem1122980 _26340 h) (@lem1122977 _26340 h)). Qed.
Lemma lem1122983 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : @I (_26340 -> Prop) P h.
Proof. exact (proj1 (@lem1121738 _26340 Q h P t h1)). Qed.
Lemma lem1122984 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term223 _26340 P h.
Proof. exact (fun h0 : term185 _26340 P h => @lem1122983 _26340 Q h P t h1). Qed.
Lemma lem1122986 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1122987 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) : (term223 _26340 P h) = (@I (_26340 -> Prop) P h).
Proof. exact (@lem1122986 (@I (_26340 -> Prop) P h)). Qed.
Lemma lem1122988 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : @I (_26340 -> Prop) P h.
Proof. exact (EQ_MP (@lem1122987 _26340 P h) (@lem1122984 _26340 Q h P t h1)). Qed.
Lemma lem1123006 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1123007 {_26340 : Type'} (Q : _26340 -> Prop) (P : _26340 -> Prop) (_18268 : _26340) : (term224 _26340 P Q _18268) = (term225 _26340 Q P _18268).
Proof. exact (@lem1123006 (@I (_26340 -> Prop) Q _18268) (term185 _26340 P _18268)). Qed.
Lemma lem1123013 {_26340 : Type'} (_18268 : _26340) (h : _26340) : (term226 _26340 _18268 h) = (term226 _26340 _18268 h).
Proof. exact (eq_refl (term226 _26340 _18268 h)). Qed.
Lemma lem1123014 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (P : _26340 -> Prop) (_18268 : _26340) : (term218 _26340 h P Q _18268) = (term227 _26340 h Q P _18268).
Proof. exact (MK_COMB (@lem1123013 _26340 _18268 h) (@lem1123007 _26340 Q P _18268)). Qed.
Lemma lem1123018 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1123019 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : (term227 _26340 h Q P _18268) = (term228 _26340 Q h P _18268).
Proof. exact (@lem1123018 (@I (_26340 -> Prop) Q _18268) (term206 _26340 _18268 h) (term185 _26340 P _18268)). Qed.
Lemma lem1123037 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : (term218 _26340 h P Q _18268) = (term228 _26340 Q h P _18268).
Proof. exact (TRANS (@lem1123014 _26340 h Q P _18268) (@lem1123019 _26340 Q h P _18268)). Qed.
Lemma lem1123038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1123039 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : (term229 _26340 h P Q _18268) = (term230 _26340 Q h P _18268).
Proof. exact (MK_COMB (@lem1123038) (@lem1123037 _26340 Q h P _18268)). Qed.
Lemma lem1123057 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : (term228 _26340 Q h P _18268) = (term228 _26340 Q h P _18268).
Proof. exact (eq_refl (term228 _26340 Q h P _18268)). Qed.
Lemma lem1123058 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : ((term218 _26340 h P Q _18268) = (term228 _26340 Q h P _18268)) = ((term228 _26340 Q h P _18268) = (term228 _26340 Q h P _18268)).
Proof. exact (MK_COMB (@lem1123039 _26340 Q h P _18268) (@lem1123057 _26340 Q h P _18268)). Qed.
Lemma lem1123060 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1123061 (x : Prop) : (x = x) = True.
Proof. exact (@lem1123060 Prop x). Qed.
Lemma lem1123062 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : ((term228 _26340 Q h P _18268) = (term228 _26340 Q h P _18268)) = True.
Proof. exact (@lem1123061 (term228 _26340 Q h P _18268)). Qed.
Lemma lem1123063 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : ((term218 _26340 h P Q _18268) = (term228 _26340 Q h P _18268)) = True.
Proof. exact (TRANS (@lem1123058 _26340 Q h P _18268) (@lem1123062 _26340 Q h P _18268)). Qed.
Lemma lem1123064 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : True = ((term218 _26340 h P Q _18268) = (term228 _26340 Q h P _18268)).
Proof. exact (SYM (@lem1123063 _26340 Q h P _18268)). Qed.
Lemma lem1123065 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : (term218 _26340 h P Q _18268) = (term228 _26340 Q h P _18268).
Proof. exact (EQ_MP (@lem1123064 _26340 Q h P _18268) (@lem0)). Qed.
Lemma lem1123066 {_26340 : Type'} (_18268 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term228 _26340 Q h P _18268.
Proof. exact (EQ_MP (@lem1123065 _26340 Q h P _18268) (@lem1122263 _26340 _18268 Q h P t h1)). Qed.
Lemma lem1123068 (b : Prop) (a : Prop) : (a \/ b) = (term231 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1123069 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18268 : _26340) : (term228 _26340 Q h P _18268) = (term232 _26340 h P Q _18268).
Proof. exact (@lem1123068 (term211 _26340 h P _18268) (@I (_26340 -> Prop) Q _18268)). Qed.
Lemma lem1123071 (a : Prop) (b : Prop) : (term233 a b) = (term234 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1123072 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : (term235 _26340 h P _18268) = (term236 _26340 h P _18268).
Proof. exact (@lem1123071 (term206 _26340 _18268 h) (term185 _26340 P _18268)). Qed.
Lemma lem1123074 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1123075 {_26340 : Type'} (_18268 : _26340) (h : _26340) : (term237 _26340 _18268 h) = (_18268 = h).
Proof. exact (@lem1123074 (_18268 = h)). Qed.
Lemma lem1123076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1123077 {_26340 : Type'} (_18268 : _26340) (h : _26340) : (term238 _26340 _18268 h) = (term239 _26340 _18268 h).
Proof. exact (MK_COMB (@lem1123076) (@lem1123075 _26340 _18268 h)). Qed.
Lemma lem1123079 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1123080 {_26340 : Type'} (P : _26340 -> Prop) (_18268 : _26340) : (term240 _26340 P _18268) = (@I (_26340 -> Prop) P _18268).
Proof. exact (@lem1123079 (@I (_26340 -> Prop) P _18268)). Qed.
Lemma lem1123081 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : (term236 _26340 h P _18268) = (term241 _26340 h P _18268).
Proof. exact (MK_COMB (@lem1123077 _26340 _18268 h) (@lem1123080 _26340 P _18268)). Qed.
Lemma lem1123082 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : (term235 _26340 h P _18268) = (term241 _26340 h P _18268).
Proof. exact (TRANS (@lem1123072 _26340 h P _18268) (@lem1123081 _26340 h P _18268)). Qed.
Lemma lem1123083 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1123084 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (_18268 : _26340) : (term242 _26340 h P _18268) = (term243 _26340 h P _18268).
Proof. exact (MK_COMB (@lem1123083) (@lem1123082 _26340 h P _18268)). Qed.
Lemma lem1123085 {_26340 : Type'} (Q : _26340 -> Prop) (_18268 : _26340) : (@I (_26340 -> Prop) Q _18268) = (@I (_26340 -> Prop) Q _18268).
Proof. exact (eq_refl (@I (_26340 -> Prop) Q _18268)). Qed.
Lemma lem1123086 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18268 : _26340) : (term232 _26340 h P Q _18268) = (term244 _26340 h P Q _18268).
Proof. exact (MK_COMB (@lem1123084 _26340 h P _18268) (@lem1123085 _26340 Q _18268)). Qed.
Lemma lem1123087 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (_18268 : _26340) : (term228 _26340 Q h P _18268) = (term244 _26340 h P Q _18268).
Proof. exact (TRANS (@lem1123069 _26340 h P Q _18268) (@lem1123086 _26340 h P Q _18268)). Qed.
Lemma lem1123089 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term245 _26340 P h.
Proof. exact (conj (@lem1122981 _26340 h) (@lem1122988 _26340 Q h P t h1)). Qed.
Lemma lem1123091 {_26340 : Type'} (_18268 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term244 _26340 h P Q _18268.
Proof. exact (EQ_MP (@lem1123087 _26340 h P Q _18268) (@lem1123066 _26340 _18268 Q h P t h1)). Qed.
Lemma lem1123092 {_26340 : Type'} (_18268 : _26340) (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term244 _26340 h P Q _18268.
Proof. exact (@lem1123091 _26340 _18268 Q h P t h1). Qed.
Lemma lem1123093 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term246 _26340 P Q h.
Proof. exact (@lem1123092 _26340 h Q h P t h1). Qed.
Lemma lem1123096 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : @I (_26340 -> Prop) Q h.
Proof. exact (@lem1123093 _26340 Q h P t h1 (@lem1123089 _26340 Q h P t h1)). Qed.
Lemma lem1123097 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : term223 _26340 Q h.
Proof. exact (fun h0 : term185 _26340 Q h => @lem1123096 _26340 Q h P t h1). Qed.
Lemma lem1123099 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1123100 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) : (term223 _26340 Q h) = (@I (_26340 -> Prop) Q h).
Proof. exact (@lem1123099 (@I (_26340 -> Prop) Q h)). Qed.
Lemma lem1123101 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) : @I (_26340 -> Prop) Q h.
Proof. exact (EQ_MP (@lem1123100 _26340 Q h) (@lem1123097 _26340 Q h P t h1)). Qed.
Lemma lem1123104 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1123106 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) : (term185 _26340 Q h) = (term247 _26340 Q h).
Proof. exact (@lem1123104 (@I (_26340 -> Prop) Q h)). Qed.
Lemma lem1123109 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (h1 : term185 _26340 Q h) : term247 _26340 Q h.
Proof. exact (EQ_MP (@lem1123106 _26340 Q h) (@lem1122251 _26340 Q h h1)). Qed.
Lemma lem1123112 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (@lem1123109 _26340 Q h h1 (@lem1123101 _26340 Q h P t h2)). Qed.
Lemma lem1123113 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : term248.
Proof. exact (fun h0 : ~ False => @lem1123112 _26340 Q h P t h1 h2). Qed.
Lemma lem1123115 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1123116 : term248 = False.
Proof. exact (@lem1123115 False). Qed.
Lemma lem1123117 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123116) (@lem1123113 _26340 Q h P t h1 h2)). Qed.
Lemma lem1123182 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : @List.Forall _26340 Q t) : @List.Forall _26340 Q t.
Proof. exact (h1). Qed.
Lemma lem1123183 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : @List.Forall _26340 Q t) : term268 _26340 Q t.
Proof. exact (fun h0 : term121 _26340 Q t => @lem1123182 _26340 Q t h1). Qed.
Lemma lem1123185 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1123186 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (term268 _26340 Q t) = (@List.Forall _26340 Q t).
Proof. exact (@lem1123185 (@List.Forall _26340 Q t)). Qed.
Lemma lem1123187 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : @List.Forall _26340 Q t) : @List.Forall _26340 Q t.
Proof. exact (EQ_MP (@lem1123186 _26340 Q t) (@lem1123183 _26340 Q t h1)). Qed.
Lemma lem1123190 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1123192 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (term121 _26340 Q t) = (term269 _26340 Q t).
Proof. exact (@lem1123190 (@List.Forall _26340 Q t)). Qed.
Lemma lem1123195 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) : term269 _26340 Q t.
Proof. exact (EQ_MP (@lem1123192 _26340 Q t) (@lem1122283 _26340 Q t h1)). Qed.
Lemma lem1123198 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : False.
Proof. exact (@lem1123195 _26340 Q t h1 (@lem1123187 _26340 Q t h2)). Qed.
Lemma lem1123199 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : term248.
Proof. exact (fun h0 : ~ False => @lem1123198 _26340 Q t h1 h2). Qed.
Lemma lem1123201 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1123202 : term248 = False.
Proof. exact (@lem1123201 False). Qed.
Lemma lem1123203 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : False.
Proof. exact (EQ_MP (@lem1123202) (@lem1123199 _26340 Q t h1 h2)). Qed.
Lemma lem1123204 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : (term121 _26340 Q t) = False.
Proof. exact (prop_ext (fun h3 : term121 _26340 Q t => @lem1123203 _26340 Q t h1 h2) (fun h3 : False => @lem1122283 _26340 Q t h1)). Qed.
Lemma lem1123205 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : False.
Proof. exact (EQ_MP (@lem1123204 _26340 Q t h1 h2) (@lem1122283 _26340 Q t h1)). Qed.
Lemma lem1123206 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : (@List.Forall _26340 Q t) = False.
Proof. exact (prop_ext (fun h3 : @List.Forall _26340 Q t => @lem1123205 _26340 Q t h1 h2) (fun h3 : False => @lem1122281 _26340 Q t h2)). Qed.
Lemma lem1123207 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : False.
Proof. exact (EQ_MP (@lem1123206 _26340 Q t h1 h2) (@lem1122281 _26340 Q t h2)). Qed.
Lemma lem1123208 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : (term185 _26340 Q h) = False.
Proof. exact (prop_ext (fun h3 : term185 _26340 Q h => @lem1123117 _26340 Q h P t h1 h2) (fun h3 : False => @lem1122251 _26340 Q h h1)). Qed.
Lemma lem1123209 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123208 _26340 Q h P t h1 h2) (@lem1122251 _26340 Q h h1)). Qed.
Lemma lem1123210 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : (term121 _26340 P t) = False.
Proof. exact (prop_ext (fun h3 : term121 _26340 P t => @lem1122909 _26340 Q h P t h1 h2) (fun h3 : False => @lem1122217 _26340 P t h1)). Qed.
Lemma lem1123211 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123210 _26340 Q h P t h1 h2) (@lem1122217 _26340 P t h1)). Qed.
Lemma lem1123212 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : (term121 _26340 P t) = False.
Proof. exact (prop_ext (fun h3 : term121 _26340 P t => @lem1122823 _26340 Q h P t h1 h2) (fun h3 : False => @lem1122185 _26340 P t h1)). Qed.
Lemma lem1123213 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123212 _26340 Q h P t h1 h2) (@lem1122185 _26340 P t h1)). Qed.
Lemma lem1123214 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : (term185 _26340 Q h) = False.
Proof. exact (prop_ext (fun h3 : term185 _26340 Q h => @lem1122515 _26340 Q h P t h1 h2) (fun h3 : False => @lem1122119 _26340 Q h h1)). Qed.
Lemma lem1123215 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123214 _26340 Q h P t h1 h2) (@lem1122119 _26340 Q h h1)). Qed.
Lemma lem1123216 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : (term121 _26340 Q t) = False.
Proof. exact (prop_ext (fun h3 : term121 _26340 Q t => @lem1123207 _26340 Q t h1 h2) (fun h3 : False => @lem1122077 _26340 Q t h1)). Qed.
Lemma lem1123217 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : False.
Proof. exact (EQ_MP (@lem1123216 _26340 Q t h1 h2) (@lem1122077 _26340 Q t h1)). Qed.
Lemma lem1123218 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : (@List.Forall _26340 Q t) = False.
Proof. exact (prop_ext (fun h3 : @List.Forall _26340 Q t => @lem1123217 _26340 Q t h1 h2) (fun h3 : False => @lem1122073 _26340 Q t h2)). Qed.
Lemma lem1123219 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : False.
Proof. exact (EQ_MP (@lem1123218 _26340 Q t h1 h2) (@lem1122073 _26340 Q t h2)). Qed.
Lemma lem1123220 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : (term185 _26340 Q h) = False.
Proof. exact (prop_ext (fun h3 : term185 _26340 Q h => @lem1123209 _26340 Q h P t h1 h2) (fun h3 : False => @lem1122026 _26340 Q h h1)). Qed.
Lemma lem1123221 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123220 _26340 Q h P t h1 h2) (@lem1122026 _26340 Q h h1)). Qed.
Lemma lem1123222 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : (term121 _26340 P t) = False.
Proof. exact (prop_ext (fun h3 : term121 _26340 P t => @lem1123211 _26340 Q h P t h1 h2) (fun h3 : False => @lem1121971 _26340 P t h1)). Qed.
Lemma lem1123223 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123222 _26340 Q h P t h1 h2) (@lem1121971 _26340 P t h1)). Qed.
Lemma lem1123224 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : (term121 _26340 P t) = False.
Proof. exact (prop_ext (fun h3 : term121 _26340 P t => @lem1123213 _26340 Q h P t h1 h2) (fun h3 : False => @lem1121920 _26340 P t h1)). Qed.
Lemma lem1123225 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123224 _26340 Q h P t h1 h2) (@lem1121920 _26340 P t h1)). Qed.
Lemma lem1123226 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : (term185 _26340 Q h) = False.
Proof. exact (prop_ext (fun h3 : term185 _26340 Q h => @lem1123215 _26340 Q h P t h1 h2) (fun h3 : False => @lem1121814 _26340 Q h h1)). Qed.
Lemma lem1123227 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123226 _26340 Q h P t h1 h2) (@lem1121814 _26340 Q h h1)). Qed.
Lemma lem1123228 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : (term121 _26340 Q t) = False.
Proof. exact (prop_ext (fun h3 : term121 _26340 Q t => @lem1123219 _26340 Q t h1 h2) (fun h3 : False => @lem1122077 _26340 Q t h1)). Qed.
Lemma lem1123229 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : False.
Proof. exact (EQ_MP (@lem1123228 _26340 Q t h1 h2) (@lem1122077 _26340 Q t h1)). Qed.
Lemma lem1123230 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : (@List.Forall _26340 Q t) = False.
Proof. exact (prop_ext (fun h3 : @List.Forall _26340 Q t => @lem1123229 _26340 Q t h1 h2) (fun h3 : False => @lem1122073 _26340 Q t h2)). Qed.
Lemma lem1123231 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 Q t) (h2 : @List.Forall _26340 Q t) : False.
Proof. exact (EQ_MP (@lem1123230 _26340 Q t h1 h2) (@lem1122073 _26340 Q t h2)). Qed.
Lemma lem1123232 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : (term185 _26340 Q h) = False.
Proof. exact (prop_ext (fun h3 : term185 _26340 Q h => @lem1123221 _26340 Q h P t h1 h2) (fun h3 : False => @lem1122026 _26340 Q h h1)). Qed.
Lemma lem1123233 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123232 _26340 Q h P t h1 h2) (@lem1122026 _26340 Q h h1)). Qed.
Lemma lem1123234 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : (term121 _26340 P t) = False.
Proof. exact (prop_ext (fun h3 : term121 _26340 P t => @lem1123223 _26340 Q h P t h1 h2) (fun h3 : False => @lem1121971 _26340 P t h1)). Qed.
Lemma lem1123235 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123234 _26340 Q h P t h1 h2) (@lem1121971 _26340 P t h1)). Qed.
Lemma lem1123236 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : (term121 _26340 P t) = False.
Proof. exact (prop_ext (fun h3 : term121 _26340 P t => @lem1123225 _26340 Q h P t h1 h2) (fun h3 : False => @lem1121920 _26340 P t h1)). Qed.
Lemma lem1123237 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term121 _26340 P t) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123236 _26340 Q h P t h1 h2) (@lem1121920 _26340 P t h1)). Qed.
Lemma lem1123238 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : (term185 _26340 Q h) = False.
Proof. exact (prop_ext (fun h3 : term185 _26340 Q h => @lem1123227 _26340 Q h P t h1 h2) (fun h3 : False => @lem1121814 _26340 Q h h1)). Qed.
Lemma lem1123239 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term185 _26340 Q h) (h2 : term71 _26340 Q h P t) : False.
Proof. exact (EQ_MP (@lem1123238 _26340 Q h P t h1 h2) (@lem1121814 _26340 Q h h1)). Qed.
Lemma lem1123240 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term108 _26340 h Q t) (h2 : term71 _26340 Q h P t) (h3 : @List.Forall _26340 Q t) : False.
Proof. exact (or_elim (@lem1121689 _26340 h Q t h1) (fun h0 : term185 _26340 Q h => @lem1123233 _26340 Q h P t h0 h2) (fun h0 : term121 _26340 Q t => @lem1123231 _26340 Q t h0 h3)). Qed.
Lemma lem1123241 {_26340 : Type'} (Q : _26340 -> Prop) (h : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term108 _26340 h Q t) (h2 : term121 _26340 P t) (h3 : term71 _26340 Q h P t) : False.
Proof. exact (or_elim (@lem1121689 _26340 h Q t h1) (fun h0 : term185 _26340 Q h => @lem1123237 _26340 Q h P t h2 h3) (fun h0 : term121 _26340 Q t => @lem1123235 _26340 Q h P t h2 h3)). Qed.
Lemma lem1123242 {_26340 : Type'} (h : _26340) (t : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) (h1 : term108 _26340 h Q t) (h2 : term71 _26340 Q h P t) (h3 : term200 _26340 t P Q x) : False.
Proof. exact (or_elim (@lem1121689 _26340 h Q t h1) (fun h0 : term185 _26340 Q h => @lem1123239 _26340 Q h P t h0 h2) (fun h0 : term121 _26340 Q t => @lem1122737 _26340 h t P Q x h2 h3)). Qed.
Lemma lem1123243 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (x : _26340) (P : _26340 -> Prop) (t : list _26340) (h1 : term108 _26340 h Q t) (h2 : term71 _26340 Q h P t) (h3 : term202 _26340 Q x P t) : False.
Proof. exact (or_elim (@lem1121742 _26340 Q x P t h3) (fun h0 : term200 _26340 t P Q x => @lem1123242 _26340 h t P Q x h1 h2 h0) (fun h0 : term121 _26340 P t => @lem1123241 _26340 Q h P t h1 h0 h2)). Qed.
Lemma lem1123244 {_26340 : Type'} (h : _26340) (x : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term108 _26340 h Q t) (h2 : term71 _26340 Q h P t) (h3 : term161 _26340 x P Q t) : False.
Proof. exact (or_elim (@lem1121737 _26340 x P Q t h3) (fun h0 : term202 _26340 Q x P t => @lem1123243 _26340 h Q x P t h1 h2 h0) (fun h0 : @List.Forall _26340 Q t => @lem1123240 _26340 h P Q t h1 h2 h0)). Qed.
Lemma lem1123245 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term108 _26340 h Q t) (h2 : term71 _26340 Q h P t) (h3 : term15 _26340 P Q t) : False.
Proof. exact (ex_elim (@lem1121524 _26340 P Q t h3) (fun x : _26340 => fun h0 : term163 _26340 P Q t x => @lem1123244 _26340 h x P Q t h1 h2 h0)). Qed.
Lemma lem1123246 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term108 _26340 h Q t) (h2 : term71 _26340 Q h P t) (h3 : term15 _26340 P Q t) : (term108 _26340 h Q t) = False.
Proof. exact (prop_ext (fun h4 : term108 _26340 h Q t => @lem1123245 _26340 h P Q t h1 h2 h3) (fun h4 : False => @lem1121386 _26340 h Q t h1)). Qed.
Lemma lem1123247 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term108 _26340 h Q t) (h2 : term71 _26340 Q h P t) (h3 : term15 _26340 P Q t) : False.
Proof. exact (EQ_MP (@lem1123246 _26340 h P Q t h1 h2 h3) (@lem1121386 _26340 h Q t h1)). Qed.
Lemma lem1123248 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) (h2 : term15 _26340 P Q t) : term107 _26340 h Q t.
Proof. exact (fun h0 : term108 _26340 h Q t => @lem1123247 _26340 h P Q t h0 h1 h2). Qed.
Lemma lem1123249 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term71 _26340 Q h P t) (h2 : term15 _26340 P Q t) : term69 _26340 h Q t.
Proof. exact (EQ_MP (@lem1121385 _26340 h Q t) (@lem1123248 _26340 h P Q t h1 h2)). Qed.
Lemma lem1123250 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term15 _26340 P Q t) : term74 _26340 P h Q t.
Proof. exact (fun h0 : term71 _26340 Q h P t => @lem1123249 _26340 h P Q t h0 h1). Qed.
Lemma lem1123251 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : term84 _26340 P h Q t.
Proof. exact (fun h0 : term15 _26340 P Q t => @lem1123250 _26340 h P Q t h0). Qed.
Lemma lem1123256 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : term88 _26340 h Q t.
Proof. exact (fun P : _26340 -> Prop => @lem1123251 _26340 P h Q t). Qed.
Lemma lem1123261 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : term92 _26340 Q t.
Proof. exact (fun h : _26340 => @lem1123256 _26340 h Q t). Qed.
Lemma lem1123266 {_26340 : Type'} (t : list _26340) : term96 _26340 t.
Proof. exact (fun Q : _26340 -> Prop => @lem1123261 _26340 Q t). Qed.
Lemma lem1123271 {_26340 : Type'} : term100 _26340.
Proof. exact (fun t : list _26340 => @lem1123266 _26340 t). Qed.
Lemma lem1123272 {_26340 : Type'} : term99 _26340.
Proof. exact (EQ_MP (@lem1121379 _26340) (@lem1123271 _26340)). Qed.
Lemma lem1123273 {_26340 : Type'} (t : list _26340) : term270 _26340 t.
Proof. exact (@lem1123272 _26340 t). Qed.
Lemma lem1123274 {_26340 : Type'} (t : list _26340) : (term270 _26340 t) = (term95 _26340 t).
Proof. exact (eq_refl (term270 _26340 t)). Qed.
Lemma lem1123275 {_26340 : Type'} (t : list _26340) : term95 _26340 t.
Proof. exact (EQ_MP (@lem1123274 _26340 t) (@lem1123273 _26340 t)). Qed.
Lemma lem1123276 {_26340 : Type'} (t : list _26340) (Q : _26340 -> Prop) : term271 _26340 t Q.
Proof. exact (@lem1123275 _26340 t Q). Qed.
Lemma lem1123277 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : (term271 _26340 t Q) = (term91 _26340 Q t).
Proof. exact (eq_refl (term271 _26340 t Q)). Qed.
Lemma lem1123278 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) : term91 _26340 Q t.
Proof. exact (EQ_MP (@lem1123277 _26340 Q t) (@lem1123276 _26340 t Q)). Qed.
Lemma lem1123279 {_26340 : Type'} (Q : _26340 -> Prop) (t : list _26340) (h : _26340) : term272 _26340 Q t h.
Proof. exact (@lem1123278 _26340 Q t h). Qed.
Lemma lem1123280 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term272 _26340 Q t h) = (term87 _26340 h Q t).
Proof. exact (eq_refl (term272 _26340 Q t h)). Qed.
Lemma lem1123281 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : term87 _26340 h Q t.
Proof. exact (EQ_MP (@lem1123280 _26340 h Q t) (@lem1123279 _26340 Q t h)). Qed.
Lemma lem1123282 {_26340 : Type'} (h : _26340) (Q : _26340 -> Prop) (t : list _26340) (P : _26340 -> Prop) : term273 _26340 h Q t P.
Proof. exact (@lem1123281 _26340 h Q t P). Qed.
Lemma lem1123283 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : (term273 _26340 h Q t P) = (term78 _26340 P h Q t).
Proof. exact (eq_refl (term273 _26340 h Q t P)). Qed.
Lemma lem1123284 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : term78 _26340 P h Q t.
Proof. exact (EQ_MP (@lem1123283 _26340 P h Q t) (@lem1123282 _26340 h Q t P)). Qed.
Lemma lem1123286 {_26340 : Type'} (P : _26340 -> Prop) (h : _26340) (Q : _26340 -> Prop) (t : list _26340) : term78 _26340 P h Q t.
Proof. exact (@lem1121157 _26340 P h Q t (@lem1123284 _26340 P h Q t)). Qed.
Lemma lem1123287 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term15 _26340 P Q t) : term76 _26340 P h Q t.
Proof. exact (@lem1123286 _26340 P h Q t (@lem1121014 _26340 P Q t h1)). Qed.
Lemma lem1123288 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term77 _26340 P h Q t) (h2 : term15 _26340 P Q t) : False.
Proof. exact (@lem1123287 _26340 h P Q t h2 (@lem1121141 _26340 P h Q t h1)). Qed.
Lemma lem1123289 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term77 _26340 P h Q t) (h2 : term15 _26340 P Q t) : (term77 _26340 P h Q t) = False.
Proof. exact (prop_ext (fun h3 : term77 _26340 P h Q t => @lem1123288 _26340 h P Q t h1 h2) (fun h3 : False => @lem1121141 _26340 P h Q t h1)). Qed.
Lemma lem1123290 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term77 _26340 P h Q t) (h2 : term15 _26340 P Q t) : False.
Proof. exact (EQ_MP (@lem1123289 _26340 h P Q t h1 h2) (@lem1121141 _26340 P h Q t h1)). Qed.
Lemma lem1123291 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term15 _26340 P Q t) : term76 _26340 P h Q t.
Proof. exact (fun h0 : term77 _26340 P h Q t => @lem1123290 _26340 h P Q t h0 h1). Qed.
Lemma lem1123292 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term15 _26340 P Q t) : term74 _26340 P h Q t.
Proof. exact (EQ_MP (@lem1121140 _26340 P h Q t) (@lem1123291 _26340 h P Q t h1)). Qed.
Lemma lem1123293 {_26340 : Type'} (h : _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (t : list _26340) (h1 : term15 _26340 P Q t) : term19 _26340 P Q h t.
Proof. exact (EQ_MP (@lem1121136 _26340 P Q h t) (@lem1123292 _26340 h P Q t h1)). Qed.
Lemma lem1123294 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (h : _26340) (t : list _26340) : term21 _26340 P Q h t.
Proof. exact (fun h0 : term15 _26340 P Q t => @lem1123293 _26340 h P Q t h0). Qed.
Lemma lem1123299 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (h : _26340) : term25 _26340 P Q h.
Proof. exact (fun t : list _26340 => @lem1123294 _26340 P Q h t). Qed.
Lemma lem1123304 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : term29 _26340 P Q.
Proof. exact (fun h : _26340 => @lem1123299 _26340 P Q h). Qed.
Lemma lem1123305 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : term31 _26340 P Q.
Proof. exact (conj (@lem1121076 _26340 P Q) (@lem1123304 _26340 P Q)). Qed.
Lemma lem1123306 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : term36 _26340 P Q.
Proof. exact (@lem1121013 _26340 P Q (@lem1123305 _26340 P Q)). Qed.
Lemma lem1123311 {_26340 : Type'} (P : _26340 -> Prop) : term274 _26340 P.
Proof. exact (fun Q : _26340 -> Prop => @lem1123306 _26340 P Q). Qed.
Lemma lem1123316 {_26340 : Type'} : term275 _26340.
Proof. exact (fun P : _26340 -> Prop => @lem1123311 _26340 P). Qed.

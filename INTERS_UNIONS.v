Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_UNIONS_term_abbrevs.
Require Import DIFF_INTERS_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3471974 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (h1 : (term0 _90037 u s) = (term1 _90037 s u)) : (term0 _90037 u s) = (term1 _90037 s u).
Proof. exact (h1). Qed.
Lemma lem3471975 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (h1 : (term0 _90037 u s) = (term1 _90037 s u)) : (term1 _90037 s u) = (term0 _90037 u s).
Proof. exact (SYM (@lem3471974 _90037 s u h1)). Qed.
Lemma lem3471976 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (h1 : (term1 _90037 s u) = (term0 _90037 u s)) : (term1 _90037 s u) = (term0 _90037 u s).
Proof. exact (h1). Qed.
Lemma lem3471977 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (h1 : (term1 _90037 s u) = (term0 _90037 u s)) : (term0 _90037 u s) = (term1 _90037 s u).
Proof. exact (SYM (@lem3471976 _90037 u s h1)). Qed.
Lemma lem3471978 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) : ((term0 _90037 u s) = (term1 _90037 s u)) = ((term1 _90037 s u) = (term0 _90037 u s)).
Proof. exact (prop_ext (fun h1 : (term0 _90037 u s) = (term1 _90037 s u) => @lem3471975 _90037 s u h1) (fun h1 : (term1 _90037 s u) = (term0 _90037 u s) => @lem3471977 _90037 u s h1)). Qed.
Lemma lem3471979 {_90037 : Type'} (u : _90037 -> Prop) : (term2 _90037 u) = (term3 _90037 u).
Proof. exact (fun_ext (fun s : type686 _90037 => @lem3471978 _90037 u s)). Qed.
Lemma lem3471980 {_90037 : Type'} : (@all ((_90037 -> Prop) -> Prop)) = (@all ((_90037 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90037 -> Prop) -> Prop))). Qed.
Lemma lem3471981 {_90037 : Type'} (u : _90037 -> Prop) : (term4 _90037 u) = (term5 _90037 u).
Proof. exact (MK_COMB (@lem3471980 _90037) (@lem3471979 _90037 u)). Qed.
Lemma lem3471982 {_90037 : Type'} : (term6 _90037) = (term7 _90037).
Proof. exact (fun_ext (fun u : _90037 -> Prop => @lem3471981 _90037 u)). Qed.
Lemma lem3471983 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3471984 {_90037 : Type'} : (term8 _90037) = (term9 _90037).
Proof. exact (MK_COMB (@lem3471983 _90037) (@lem3471982 _90037)). Qed.
Lemma lem3471985 {_90037 : Type'} : term9 _90037.
Proof. exact (EQ_MP (@lem3471984 _90037) (@lem3471961 _90037)). Qed.
Lemma lem3471986 {_90037 : Type'} (u : _90037 -> Prop) : term10 _90037 u.
Proof. exact (@lem3471985 _90037 u). Qed.
Lemma lem3471987 {_90037 : Type'} (u : _90037 -> Prop) : (term10 _90037 u) = (term5 _90037 u).
Proof. exact (eq_refl (term10 _90037 u)). Qed.
Lemma lem3471988 {_90037 : Type'} (u : _90037 -> Prop) : term5 _90037 u.
Proof. exact (EQ_MP (@lem3471987 _90037 u) (@lem3471986 _90037 u)). Qed.
Lemma lem3471989 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) : term11 _90037 u s.
Proof. exact (@lem3471988 _90037 u s). Qed.
Lemma lem3471990 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) : (term11 _90037 u s) = ((term1 _90037 s u) = (term0 _90037 u s)).
Proof. exact (eq_refl (term11 _90037 u s)). Qed.
Lemma lem3471999 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) : (term1 _90037 s u) = (term0 _90037 u s).
Proof. exact (EQ_MP (@lem3471990 _90037 u s) (@lem3471989 _90037 u s)). Qed.
Lemma lem3472000 {_90072 : Type'} (u : _90072 -> Prop) (s : type686 _90072) : (term1 _90072 s u) = (term0 _90072 u s).
Proof. exact (@lem3471999 _90072 u s). Qed.
Lemma lem3472001 {_90072 : Type'} (s : type686 _90072) : (term12 _90072 s) = (term13 _90072 s).
Proof. exact (@lem3472000 _90072 (@UNIV _90072) s). Qed.
Lemma lem3472002 {_90072 : Type'} : (@DIFF _90072 (@UNIV _90072)) = (@DIFF _90072 (@UNIV _90072)).
Proof. exact (eq_refl (@DIFF _90072 (@UNIV _90072))). Qed.
Lemma lem3472003 {_90072 : Type'} (s : type686 _90072) : (term14 _90072 s) = (term15 _90072 s).
Proof. exact (MK_COMB (@lem3472002 _90072) (@lem3472001 _90072 s)). Qed.
Lemma lem3472004 {_90072 : Type'} (s : type686 _90072) : (term16 _90072 s) = (term16 _90072 s).
Proof. exact (eq_refl (term16 _90072 s)). Qed.
Lemma lem3472005 {_90072 : Type'} (s : type686 _90072) : ((@INTERS _90072 s) = (term14 _90072 s)) = ((@INTERS _90072 s) = (term15 _90072 s)).
Proof. exact (MK_COMB (@lem3472004 _90072 s) (@lem3472003 _90072 s)). Qed.
Lemma lem3472008 {_90072 : Type'} : (term17 _90072) = (term18 _90072).
Proof. exact (fun_ext (fun s : type686 _90072 => @lem3472005 _90072 s)). Qed.
Lemma lem3472009 {_90072 : Type'} : (@all ((_90072 -> Prop) -> Prop)) = (@all ((_90072 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90072 -> Prop) -> Prop))). Qed.
Lemma lem3472010 {_90072 : Type'} : (term19 _90072) = (term20 _90072).
Proof. exact (MK_COMB (@lem3472009 _90072) (@lem3472008 _90072)). Qed.
Lemma lem3472015 {_90072 : Type'} : (term20 _90072) = (term19 _90072).
Proof. exact (SYM (@lem3472010 _90072)). Qed.
Lemma lem3472023 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term21 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3472024 {_90072 : Type'} (s : _90072 -> Prop) (t : _90072 -> Prop) : (s = t) = (term21 _90072 s t).
Proof. exact (@lem3472023 _90072 s t). Qed.
Lemma lem3472025 {_90072 : Type'} (s : type686 _90072) : ((@INTERS _90072 s) = (term15 _90072 s)) = (term22 _90072 s).
Proof. exact (@lem3472024 _90072 (@INTERS _90072 s) (term15 _90072 s)). Qed.
Lemma lem3472034 {_90072 : Type'} : (term18 _90072) = (term23 _90072).
Proof. exact (fun_ext (fun s : type686 _90072 => @lem3472025 _90072 s)). Qed.
Lemma lem3472035 {_90072 : Type'} : (@all ((_90072 -> Prop) -> Prop)) = (@all ((_90072 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90072 -> Prop) -> Prop))). Qed.
Lemma lem3472036 {_90072 : Type'} : (term20 _90072) = (term24 _90072).
Proof. exact (MK_COMB (@lem3472035 _90072) (@lem3472034 _90072)). Qed.
Lemma lem3472041 {_90072 : Type'} : (term24 _90072) = (term20 _90072).
Proof. exact (SYM (@lem3472036 _90072)). Qed.
Lemma lem3472053 {A : Type'} (s : type686 A) (x : A) : (term25 A x s) = (term26 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3472054 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term25 _90072 x s) = (term26 _90072 s x).
Proof. exact (@lem3472053 _90072 s x). Qed.
Lemma lem3472062 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3472063 {_90072 : Type'} (P : type686 _90072) (x : _90072 -> Prop) : (@IN (_90072 -> Prop) x P) = (P x).
Proof. exact (@lem3472062 (_90072 -> Prop) P x). Qed.
Lemma lem3472064 {_90072 : Type'} (s : type686 _90072) (t : _90072 -> Prop) : (@IN (_90072 -> Prop) t s) = (s t).
Proof. exact (@lem3472063 _90072 s t). Qed.
Lemma lem3472065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3472066 {_90072 : Type'} (s : type686 _90072) (t : _90072 -> Prop) : (term27 _90072 t s) = (term28 _90072 s t).
Proof. exact (MK_COMB (@lem3472065) (@lem3472064 _90072 s t)). Qed.
Lemma lem3472068 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3472069 {_90072 : Type'} (P : _90072 -> Prop) (x : _90072) : (@IN _90072 x P) = (P x).
Proof. exact (@lem3472068 _90072 P x). Qed.
Lemma lem3472070 {_90072 : Type'} (t : _90072 -> Prop) (x : _90072) : (@IN _90072 x t) = (t x).
Proof. exact (@lem3472069 _90072 t x). Qed.
Lemma lem3472071 {_90072 : Type'} (s : type686 _90072) (t : _90072 -> Prop) (x : _90072) : (term29 _90072 s x t) = (term30 _90072 s t x).
Proof. exact (MK_COMB (@lem3472066 _90072 s t) (@lem3472070 _90072 t x)). Qed.
Lemma lem3472074 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term31 _90072 s x) = (term32 _90072 s x).
Proof. exact (fun_ext (fun t : _90072 -> Prop => @lem3472071 _90072 s t x)). Qed.
Lemma lem3472075 {_90072 : Type'} : (@all (_90072 -> Prop)) = (@all (_90072 -> Prop)).
Proof. exact (eq_refl (@all (_90072 -> Prop))). Qed.
Lemma lem3472076 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term26 _90072 s x) = (term33 _90072 s x).
Proof. exact (MK_COMB (@lem3472075 _90072) (@lem3472074 _90072 s x)). Qed.
Lemma lem3472081 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term25 _90072 x s) = (term33 _90072 s x).
Proof. exact (TRANS (@lem3472054 _90072 s x) (@lem3472076 _90072 s x)). Qed.
Lemma lem3472082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3472083 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term34 _90072 x s) = (term35 _90072 s x).
Proof. exact (MK_COMB (@lem3472082) (@lem3472081 _90072 s x)). Qed.
Lemma lem3472085 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term36 A x s t) = (term37 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3472086 {_90072 : Type'} (s : _90072 -> Prop) (x : _90072) (t : _90072 -> Prop) : (term36 _90072 x s t) = (term37 _90072 s x t).
Proof. exact (@lem3472085 _90072 s x t). Qed.
Lemma lem3472087 {_90072 : Type'} (x : _90072) (s : type686 _90072) : (term38 _90072 x s) = (term39 _90072 x s).
Proof. exact (@lem3472086 _90072 (@UNIV _90072) x (term13 _90072 s)). Qed.
Lemma lem3472091 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3472092 {_90072 : Type'} (x : _90072) : (@IN _90072 x (@UNIV _90072)) = True.
Proof. exact (@lem3472091 _90072 x). Qed.
Lemma lem3472093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3472094 {_90072 : Type'} (x : _90072) : (term40 _90072 x) = (and True).
Proof. exact (MK_COMB (@lem3472093) (@lem3472092 _90072 x)). Qed.
Lemma lem3472096 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term36 A x s t) = (term37 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3472097 {_90072 : Type'} (s : _90072 -> Prop) (x : _90072) (t : _90072 -> Prop) : (term36 _90072 x s t) = (term37 _90072 s x t).
Proof. exact (@lem3472096 _90072 s x t). Qed.
Lemma lem3472098 {_90072 : Type'} (x : _90072) (s : type686 _90072) : (term41 _90072 x s) = (term42 _90072 x s).
Proof. exact (@lem3472097 _90072 (@UNIV _90072) x (@INTERS _90072 s)). Qed.
Lemma lem3472102 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3472103 {_90072 : Type'} (x : _90072) : (@IN _90072 x (@UNIV _90072)) = True.
Proof. exact (@lem3472102 _90072 x). Qed.
Lemma lem3472104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3472105 {_90072 : Type'} (x : _90072) : (term40 _90072 x) = (and True).
Proof. exact (MK_COMB (@lem3472104) (@lem3472103 _90072 x)). Qed.
Lemma lem3472107 {A : Type'} (s : type686 A) (x : A) : (term25 A x s) = (term26 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3472108 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term25 _90072 x s) = (term26 _90072 s x).
Proof. exact (@lem3472107 _90072 s x). Qed.
Lemma lem3472116 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3472117 {_90072 : Type'} (P : type686 _90072) (x : _90072 -> Prop) : (@IN (_90072 -> Prop) x P) = (P x).
Proof. exact (@lem3472116 (_90072 -> Prop) P x). Qed.
Lemma lem3472118 {_90072 : Type'} (s : type686 _90072) (t : _90072 -> Prop) : (@IN (_90072 -> Prop) t s) = (s t).
Proof. exact (@lem3472117 _90072 s t). Qed.
Lemma lem3472119 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3472120 {_90072 : Type'} (s : type686 _90072) (t : _90072 -> Prop) : (term27 _90072 t s) = (term28 _90072 s t).
Proof. exact (MK_COMB (@lem3472119) (@lem3472118 _90072 s t)). Qed.
Lemma lem3472122 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3472123 {_90072 : Type'} (P : _90072 -> Prop) (x : _90072) : (@IN _90072 x P) = (P x).
Proof. exact (@lem3472122 _90072 P x). Qed.
Lemma lem3472124 {_90072 : Type'} (t : _90072 -> Prop) (x : _90072) : (@IN _90072 x t) = (t x).
Proof. exact (@lem3472123 _90072 t x). Qed.
Lemma lem3472125 {_90072 : Type'} (s : type686 _90072) (t : _90072 -> Prop) (x : _90072) : (term29 _90072 s x t) = (term30 _90072 s t x).
Proof. exact (MK_COMB (@lem3472120 _90072 s t) (@lem3472124 _90072 t x)). Qed.
Lemma lem3472128 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term31 _90072 s x) = (term32 _90072 s x).
Proof. exact (fun_ext (fun t : _90072 -> Prop => @lem3472125 _90072 s t x)). Qed.
Lemma lem3472129 {_90072 : Type'} : (@all (_90072 -> Prop)) = (@all (_90072 -> Prop)).
Proof. exact (eq_refl (@all (_90072 -> Prop))). Qed.
Lemma lem3472130 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term26 _90072 s x) = (term33 _90072 s x).
Proof. exact (MK_COMB (@lem3472129 _90072) (@lem3472128 _90072 s x)). Qed.
Lemma lem3472135 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term25 _90072 x s) = (term33 _90072 s x).
Proof. exact (TRANS (@lem3472108 _90072 s x) (@lem3472130 _90072 s x)). Qed.
Lemma lem3472136 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3472137 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term43 _90072 x s) = (term44 _90072 s x).
Proof. exact (MK_COMB (@lem3472136) (@lem3472135 _90072 s x)). Qed.
Lemma lem3472138 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term42 _90072 x s) = (term45 _90072 s x).
Proof. exact (MK_COMB (@lem3472105 _90072 x) (@lem3472137 _90072 s x)). Qed.
Lemma lem3472140 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3472141 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term45 _90072 s x) = (term44 _90072 s x).
Proof. exact (@lem3472140 (term44 _90072 s x)). Qed.
Lemma lem3472148 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term42 _90072 x s) = (term44 _90072 s x).
Proof. exact (TRANS (@lem3472138 _90072 s x) (@lem3472141 _90072 s x)). Qed.
Lemma lem3472149 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term41 _90072 x s) = (term44 _90072 s x).
Proof. exact (TRANS (@lem3472098 _90072 x s) (@lem3472148 _90072 s x)). Qed.
Lemma lem3472150 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3472151 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term46 _90072 x s) = (term47 _90072 s x).
Proof. exact (MK_COMB (@lem3472150) (@lem3472149 _90072 s x)). Qed.
Lemma lem3472153 (t : Prop) : (term48 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem3472154 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term47 _90072 s x) = (term33 _90072 s x).
Proof. exact (@lem3472153 (term33 _90072 s x)). Qed.
Lemma lem3472161 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term46 _90072 x s) = (term33 _90072 s x).
Proof. exact (TRANS (@lem3472151 _90072 s x) (@lem3472154 _90072 s x)). Qed.
Lemma lem3472162 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term39 _90072 x s) = (term49 _90072 s x).
Proof. exact (MK_COMB (@lem3472094 _90072 x) (@lem3472161 _90072 s x)). Qed.
Lemma lem3472164 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3472165 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term49 _90072 s x) = (term33 _90072 s x).
Proof. exact (@lem3472164 (term33 _90072 s x)). Qed.
Lemma lem3472172 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term39 _90072 x s) = (term33 _90072 s x).
Proof. exact (TRANS (@lem3472162 _90072 s x) (@lem3472165 _90072 s x)). Qed.
Lemma lem3472173 {_90072 : Type'} (s : type686 _90072) (x : _90072) : (term38 _90072 x s) = (term33 _90072 s x).
Proof. exact (TRANS (@lem3472087 _90072 x s) (@lem3472172 _90072 s x)). Qed.
Lemma lem3472174 {_90072 : Type'} (s : type686 _90072) (x : _90072) : ((term25 _90072 x s) = (term38 _90072 x s)) = ((term33 _90072 s x) = (term33 _90072 s x)).
Proof. exact (MK_COMB (@lem3472083 _90072 s x) (@lem3472173 _90072 s x)). Qed.
Lemma lem3472176 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3472177 (x : Prop) : (x = x) = True.
Proof. exact (@lem3472176 Prop x). Qed.
Lemma lem3472178 {_90072 : Type'} (s : type686 _90072) (x : _90072) : ((term33 _90072 s x) = (term33 _90072 s x)) = True.
Proof. exact (@lem3472177 (term33 _90072 s x)). Qed.
Lemma lem3472179 {_90072 : Type'} (x : _90072) (s : type686 _90072) : ((term25 _90072 x s) = (term38 _90072 x s)) = True.
Proof. exact (TRANS (@lem3472174 _90072 s x) (@lem3472178 _90072 s x)). Qed.
Lemma lem3472180 {_90072 : Type'} (s : type686 _90072) : (term50 _90072 s) = (term51 _90072).
Proof. exact (fun_ext (fun x : _90072 => @lem3472179 _90072 x s)). Qed.
Lemma lem3472181 {_90072 : Type'} : (@all _90072) = (@all _90072).
Proof. exact (eq_refl (@all _90072)). Qed.
Lemma lem3472182 {_90072 : Type'} (s : type686 _90072) : (term22 _90072 s) = (term52 _90072).
Proof. exact (MK_COMB (@lem3472181 _90072) (@lem3472180 _90072 s)). Qed.
Lemma lem3472184 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3472185 {_90072 : Type'} (t : Prop) : (term53 _90072 t) = t.
Proof. exact (@lem3472184 _90072 t). Qed.
Lemma lem3472186 {_90072 : Type'} : (term52 _90072) = True.
Proof. exact (@lem3472185 _90072 True). Qed.
Lemma lem3472187 {_90072 : Type'} (s : type686 _90072) : (term22 _90072 s) = True.
Proof. exact (TRANS (@lem3472182 _90072 s) (@lem3472186 _90072)). Qed.
Lemma lem3472188 {_90072 : Type'} : (term23 _90072) = (term54 _90072).
Proof. exact (fun_ext (fun s : type686 _90072 => @lem3472187 _90072 s)). Qed.
Lemma lem3472189 {_90072 : Type'} : (@all ((_90072 -> Prop) -> Prop)) = (@all ((_90072 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90072 -> Prop) -> Prop))). Qed.
Lemma lem3472190 {_90072 : Type'} : (term24 _90072) = (term55 _90072).
Proof. exact (MK_COMB (@lem3472189 _90072) (@lem3472188 _90072)). Qed.
Lemma lem3472192 {A : Type'} (t : Prop) : (term53 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3472193 {_90072 : Type'} (t : Prop) : (term56 _90072 t) = t.
Proof. exact (@lem3472192 (type686 _90072) t). Qed.
Lemma lem3472194 {_90072 : Type'} : (term55 _90072) = True.
Proof. exact (@lem3472193 _90072 True). Qed.
Lemma lem3472195 {_90072 : Type'} : (term24 _90072) = True.
Proof. exact (TRANS (@lem3472190 _90072) (@lem3472194 _90072)). Qed.
Lemma lem3472196 {_90072 : Type'} : True = (term24 _90072).
Proof. exact (SYM (@lem3472195 _90072)). Qed.
Lemma lem3472197 {_90072 : Type'} : term24 _90072.
Proof. exact (EQ_MP (@lem3472196 _90072) (@lem0)). Qed.
Lemma lem3472198 {_90072 : Type'} : term20 _90072.
Proof. exact (EQ_MP (@lem3472041 _90072) (@lem3472197 _90072)). Qed.
Lemma lem3472199 {_90072 : Type'} : term19 _90072.
Proof. exact (EQ_MP (@lem3472015 _90072) (@lem3472198 _90072)). Qed.

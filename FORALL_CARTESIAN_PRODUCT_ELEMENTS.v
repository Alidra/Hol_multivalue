Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_CARTESIAN_PRODUCT_ELEMENTS_term_abbrevs.
Require Import CARTESIAN_PRODUCT_EQ_EMPTY_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import EXTENSIONAL_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SKOLEM_THM_spec.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm15249_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18934_spec.
Require Import thm18935_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Require Import thm3184714_spec.
Require Import thm3184717_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4446993 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4446994 {_106676 : Type'} (s : _106676 -> Prop) (t : _106676 -> Prop) : (s = t) = (term0 _106676 s t).
Proof. exact (@lem4446993 _106676 s t). Qed.
Lemma lem4446995 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : ((s i) = (@EMPTY _106676)) = (term1 _106676 _106693 s i).
Proof. exact (@lem4446994 _106676 (s i) (@EMPTY _106676)). Qed.
Lemma lem4447004 {_106693 : Type'} (i : _106693) (k : _106693 -> Prop) : (term2 _106693 i k) = (term2 _106693 i k).
Proof. exact (eq_refl (term2 _106693 i k)). Qed.
Lemma lem4447005 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term3 _106676 _106693 k s i) = (term4 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447004 _106693 i k) (@lem4446995 _106676 _106693 s i)). Qed.
Lemma lem4447008 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term5 _106676 _106693 k s) = (term6 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447005 _106676 _106693 k s i)). Qed.
Lemma lem4447009 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447010 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term7 _106676 _106693 k s) = (term8 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447009 _106693) (@lem4447008 _106676 _106693 k s)). Qed.
Lemma lem4447015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4447016 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term9 _106676 _106693 k s) = (term10 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447015) (@lem4447010 _106676 _106693 k s)). Qed.
Lemma lem4447017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447018 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term11 _106676 _106693 k s) = (term12 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447017) (@lem4447016 _106676 _106693 k s)). Qed.
Lemma lem4447029 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term13 _106676 _106693 k s) = (term13 _106676 _106693 k s).
Proof. exact (eq_refl (term13 _106676 _106693 k s)). Qed.
Lemma lem4447030 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term9 _106676 _106693 k s) = (term13 _106676 _106693 k s)) = ((term10 _106676 _106693 k s) = (term13 _106676 _106693 k s)).
Proof. exact (MK_COMB (@lem4447018 _106676 _106693 k s) (@lem4447029 _106676 _106693 k s)). Qed.
Lemma lem4447035 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term10 _106676 _106693 k s) = (term13 _106676 _106693 k s)) = ((term9 _106676 _106693 k s) = (term13 _106676 _106693 k s)).
Proof. exact (SYM (@lem4447030 _106676 _106693 k s)). Qed.
Lemma lem4447045 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4447046 {_106693 : Type'} (P : _106693 -> Prop) (x : _106693) : (@IN _106693 x P) = (P x).
Proof. exact (@lem4447045 _106693 P x). Qed.
Lemma lem4447047 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (@IN _106693 i k) = (k i).
Proof. exact (@lem4447046 _106693 k i). Qed.
Lemma lem4447048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4447049 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term2 _106693 i k) = (term14 _106693 k i).
Proof. exact (MK_COMB (@lem4447048) (@lem4447047 _106693 k i)). Qed.
Lemma lem4447057 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4447058 {_106676 : Type'} (P : _106676 -> Prop) (x : _106676) : (@IN _106676 x P) = (P x).
Proof. exact (@lem4447057 _106676 P x). Qed.
Lemma lem4447059 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term15 _106676 _106693 x s i) = (s i x).
Proof. exact (@lem4447058 _106676 (s i) x). Qed.
Lemma lem4447060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447061 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term16 _106676 _106693 x s i) = (term17 _106676 _106693 s i x).
Proof. exact (MK_COMB (@lem4447060) (@lem4447059 _106676 _106693 s i x)). Qed.
Lemma lem4447063 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4447064 {_106676 : Type'} (x : _106676) : (@IN _106676 x (@EMPTY _106676)) = False.
Proof. exact (@lem4447063 _106676 x). Qed.
Lemma lem4447065 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : ((term15 _106676 _106693 x s i) = (@IN _106676 x (@EMPTY _106676))) = ((s i x) = False).
Proof. exact (MK_COMB (@lem4447061 _106676 _106693 s i x) (@lem4447064 _106676 x)). Qed.
Lemma lem4447067 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4447068 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : ((s i x) = False) = (term18 _106676 _106693 s i x).
Proof. exact (@lem4447067 (s i x)). Qed.
Lemma lem4447069 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : ((term15 _106676 _106693 x s i) = (@IN _106676 x (@EMPTY _106676))) = (term18 _106676 _106693 s i x).
Proof. exact (TRANS (@lem4447065 _106676 _106693 s i x) (@lem4447068 _106676 _106693 s i x)). Qed.
Lemma lem4447070 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term19 _106676 _106693 s i) = (term20 _106676 _106693 s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447069 _106676 _106693 s i x)). Qed.
Lemma lem4447071 {_106676 : Type'} : (@all _106676) = (@all _106676).
Proof. exact (eq_refl (@all _106676)). Qed.
Lemma lem4447072 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term1 _106676 _106693 s i) = (term21 _106676 _106693 s i).
Proof. exact (MK_COMB (@lem4447071 _106676) (@lem4447070 _106676 _106693 s i)). Qed.
Lemma lem4447077 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term4 _106676 _106693 k s i) = (term22 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447049 _106693 k i) (@lem4447072 _106676 _106693 s i)). Qed.
Lemma lem4447080 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term6 _106676 _106693 k s) = (term23 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447077 _106676 _106693 k s i)). Qed.
Lemma lem4447081 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447082 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term8 _106676 _106693 k s) = (term24 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447081 _106693) (@lem4447080 _106676 _106693 k s)). Qed.
Lemma lem4447087 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4447088 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term10 _106676 _106693 k s) = (term25 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447087) (@lem4447082 _106676 _106693 k s)). Qed.
Lemma lem4447089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447090 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term12 _106676 _106693 k s) = (term26 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447089) (@lem4447088 _106676 _106693 k s)). Qed.
Lemma lem4447102 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4447103 {_106693 : Type'} (P : _106693 -> Prop) (x : _106693) : (@IN _106693 x P) = (P x).
Proof. exact (@lem4447102 _106693 P x). Qed.
Lemma lem4447104 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (@IN _106693 i k) = (k i).
Proof. exact (@lem4447103 _106693 k i). Qed.
Lemma lem4447105 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4447106 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term27 _106693 i k) = (term28 _106693 k i).
Proof. exact (MK_COMB (@lem4447105) (@lem4447104 _106693 k i)). Qed.
Lemma lem4447108 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4447109 {_106676 : Type'} (P : _106676 -> Prop) (x : _106676) : (@IN _106676 x P) = (P x).
Proof. exact (@lem4447108 _106676 P x). Qed.
Lemma lem4447110 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term15 _106676 _106693 x s i) = (s i x).
Proof. exact (@lem4447109 _106676 (s i) x). Qed.
Lemma lem4447111 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term29 _106676 _106693 k x s i) = (term30 _106676 _106693 k s i x).
Proof. exact (MK_COMB (@lem4447106 _106693 k i) (@lem4447110 _106676 _106693 s i x)). Qed.
Lemma lem4447114 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term31 _106676 _106693 k s i) = (term32 _106676 _106693 k s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447111 _106676 _106693 k s i x)). Qed.
Lemma lem4447115 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447116 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term33 _106676 _106693 k s i) = (term34 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447115 _106676) (@lem4447114 _106676 _106693 k s i)). Qed.
Lemma lem4447121 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term35 _106676 _106693 k s) = (term36 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447116 _106676 _106693 k s i)). Qed.
Lemma lem4447122 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4447123 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term13 _106676 _106693 k s) = (term37 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447122 _106693) (@lem4447121 _106676 _106693 k s)). Qed.
Lemma lem4447128 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term10 _106676 _106693 k s) = (term13 _106676 _106693 k s)) = ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s)).
Proof. exact (MK_COMB (@lem4447090 _106676 _106693 k s) (@lem4447123 _106676 _106693 k s)). Qed.
Lemma lem4447131 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s)) = ((term10 _106676 _106693 k s) = (term13 _106676 _106693 k s)).
Proof. exact (SYM (@lem4447128 _106676 _106693 k s)). Qed.
Lemma lem4447133 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4447134 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s)) = (term39 _106676 _106693 k s).
Proof. exact (@lem4447133 ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s))). Qed.
Lemma lem4447135 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term39 _106676 _106693 k s) = ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s)).
Proof. exact (SYM (@lem4447134 _106676 _106693 k s)). Qed.
Lemma lem4447136 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term40 _106676 _106693 k s) : term40 _106676 _106693 k s.
Proof. exact (h1). Qed.
Lemma lem4447139 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term39 _106676 _106693 k s) : term39 _106676 _106693 k s.
Proof. exact (h1). Qed.
Lemma lem4447140 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : term41 _106676 _106693 k s.
Proof. exact (fun h0 : term39 _106676 _106693 k s => @lem4447139 _106676 _106693 k s h0). Qed.
Lemma lem4447141 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term41 _106676 _106693 k s) : term41 _106676 _106693 k s.
Proof. exact (h1). Qed.
Lemma lem4447142 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term39 _106676 _106693 k s) : term39 _106676 _106693 k s.
Proof. exact (h1). Qed.
Lemma lem4447143 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term39 _106676 _106693 k s) (h2 : term41 _106676 _106693 k s) : term39 _106676 _106693 k s.
Proof. exact (@lem4447141 _106676 _106693 k s h2 (@lem4447142 _106676 _106693 k s h1)). Qed.
Lemma lem4447144 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term39 _106676 _106693 k s) : term42 _106676 _106693 k s.
Proof. exact (fun h0 : term41 _106676 _106693 k s => @lem4447143 _106676 _106693 k s h1 h0). Qed.
Lemma lem4447145 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term41 _106676 _106693 k s) : term41 _106676 _106693 k s.
Proof. exact (h1). Qed.
Lemma lem4447146 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term39 _106676 _106693 k s) (h2 : term41 _106676 _106693 k s) : term39 _106676 _106693 k s.
Proof. exact (@lem4447144 _106676 _106693 k s h1 (@lem4447145 _106676 _106693 k s h2)). Qed.
Lemma lem4447147 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term41 _106676 _106693 k s) : term41 _106676 _106693 k s.
Proof. exact (fun h0 : term39 _106676 _106693 k s => @lem4447146 _106676 _106693 k s h0 h1). Qed.
Lemma lem4447148 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : term43 _106676 _106693 k s.
Proof. exact (fun h0 : term41 _106676 _106693 k s => @lem4447147 _106676 _106693 k s h0). Qed.
Lemma lem4447151 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : term41 _106676 _106693 k s.
Proof. exact (@lem4447148 _106676 _106693 k s (@lem4447140 _106676 _106693 k s)). Qed.
Lemma lem4447152 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : term41 _106676 _106693 k s.
Proof. exact (@lem4447151 _106676 _106693 k s). Qed.
Lemma lem4447162 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4447163 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term39 _106676 _106693 k s) = (term44 _106676 _106693 k s).
Proof. exact (@lem4447162 (term40 _106676 _106693 k s)). Qed.
Lemma lem4447165 (t : Prop) : (term45 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4447166 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term44 _106676 _106693 k s) = ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s)).
Proof. exact (@lem4447165 ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s))). Qed.
Lemma lem4447167 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term39 _106676 _106693 k s) = ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s)).
Proof. exact (TRANS (@lem4447163 _106676 _106693 k s) (@lem4447166 _106676 _106693 k s)). Qed.
Lemma lem4447212 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) : (term46 _106676 _106693 s) = (term47 _106676 _106693 s).
Proof. exact (fun_ext (fun k : _106693 -> Prop => @lem4447167 _106676 _106693 k s)). Qed.
Lemma lem4447213 {_106693 : Type'} : (@all (_106693 -> Prop)) = (@all (_106693 -> Prop)).
Proof. exact (eq_refl (@all (_106693 -> Prop))). Qed.
Lemma lem4447214 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) : (term48 _106676 _106693 s) = (term49 _106676 _106693 s).
Proof. exact (MK_COMB (@lem4447213 _106693) (@lem4447212 _106676 _106693 s)). Qed.
Lemma lem4447219 {_106676 _106693 : Type'} : (term50 _106676 _106693) = (term51 _106676 _106693).
Proof. exact (fun_ext (fun s : type1470 _106676 _106693 => @lem4447214 _106676 _106693 s)). Qed.
Lemma lem4447220 {_106676 _106693 : Type'} : (@all (_106693 -> _106676 -> Prop)) = (@all (_106693 -> _106676 -> Prop)).
Proof. exact (eq_refl (@all (_106693 -> _106676 -> Prop))). Qed.
Lemma lem4447229 {_106676 _106693 : Type'} : (term52 _106676 _106693) = (term53 _106676 _106693).
Proof. exact (MK_COMB (@lem4447220 _106676 _106693) (@lem4447219 _106676 _106693)). Qed.
Lemma lem4447234 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term30 _106676 _106693 k s i x) = (term30 _106676 _106693 k s i x).
Proof. exact (eq_refl (term30 _106676 _106693 k s i x)). Qed.
Lemma lem4447235 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term32 _106676 _106693 k s i) = (term32 _106676 _106693 k s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447234 _106676 _106693 k s i x)). Qed.
Lemma lem4447236 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447237 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term34 _106676 _106693 k s i) = (term34 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447236 _106676) (@lem4447235 _106676 _106693 k s i)). Qed.
Lemma lem4447238 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term36 _106676 _106693 k s) = (term36 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447237 _106676 _106693 k s i)). Qed.
Lemma lem4447239 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4447240 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term37 _106676 _106693 k s) = (term37 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447239 _106693) (@lem4447238 _106676 _106693 k s)). Qed.
Lemma lem4447243 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term18 _106676 _106693 s i x) = (term18 _106676 _106693 s i x).
Proof. exact (eq_refl (term18 _106676 _106693 s i x)). Qed.
Lemma lem4447244 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term20 _106676 _106693 s i) = (term20 _106676 _106693 s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447243 _106676 _106693 s i x)). Qed.
Lemma lem4447245 {_106676 : Type'} : (@all _106676) = (@all _106676).
Proof. exact (eq_refl (@all _106676)). Qed.
Lemma lem4447246 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term21 _106676 _106693 s i) = (term21 _106676 _106693 s i).
Proof. exact (MK_COMB (@lem4447245 _106676) (@lem4447244 _106676 _106693 s i)). Qed.
Lemma lem4447249 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term14 _106693 k i) = (term14 _106693 k i).
Proof. exact (eq_refl (term14 _106693 k i)). Qed.
Lemma lem4447250 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term22 _106676 _106693 k s i) = (term22 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447249 _106693 k i) (@lem4447246 _106676 _106693 s i)). Qed.
Lemma lem4447251 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term23 _106676 _106693 k s) = (term23 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447250 _106676 _106693 k s i)). Qed.
Lemma lem4447252 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447253 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term24 _106676 _106693 k s) = (term24 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447252 _106693) (@lem4447251 _106676 _106693 k s)). Qed.
Lemma lem4447254 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4447255 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term25 _106676 _106693 k s) = (term25 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447254) (@lem4447253 _106676 _106693 k s)). Qed.
Lemma lem4447256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447257 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term26 _106676 _106693 k s) = (term26 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447256) (@lem4447255 _106676 _106693 k s)). Qed.
Lemma lem4447258 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s)) = ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s)).
Proof. exact (MK_COMB (@lem4447257 _106676 _106693 k s) (@lem4447240 _106676 _106693 k s)). Qed.
Lemma lem4447259 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) : (term47 _106676 _106693 s) = (term47 _106676 _106693 s).
Proof. exact (fun_ext (fun k : _106693 -> Prop => @lem4447258 _106676 _106693 k s)). Qed.
Lemma lem4447260 {_106693 : Type'} : (@all (_106693 -> Prop)) = (@all (_106693 -> Prop)).
Proof. exact (eq_refl (@all (_106693 -> Prop))). Qed.
Lemma lem4447261 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) : (term49 _106676 _106693 s) = (term49 _106676 _106693 s).
Proof. exact (MK_COMB (@lem4447260 _106693) (@lem4447259 _106676 _106693 s)). Qed.
Lemma lem4447262 {_106676 _106693 : Type'} : (term51 _106676 _106693) = (term51 _106676 _106693).
Proof. exact (fun_ext (fun s : type1470 _106676 _106693 => @lem4447261 _106676 _106693 s)). Qed.
Lemma lem4447263 {_106676 _106693 : Type'} : (@all (_106693 -> _106676 -> Prop)) = (@all (_106693 -> _106676 -> Prop)).
Proof. exact (eq_refl (@all (_106693 -> _106676 -> Prop))). Qed.
Lemma lem4447264 {_106676 _106693 : Type'} : (term53 _106676 _106693) = (term53 _106676 _106693).
Proof. exact (MK_COMB (@lem4447263 _106676 _106693) (@lem4447262 _106676 _106693)). Qed.
Lemma lem4447307 {_106676 _106693 : Type'} : (term52 _106676 _106693) = (term53 _106676 _106693).
Proof. exact (TRANS (@lem4447229 _106676 _106693) (@lem4447264 _106676 _106693)). Qed.
Lemma lem4447308 {_106676 _106693 : Type'} : (term53 _106676 _106693) = (term52 _106676 _106693).
Proof. exact (SYM (@lem4447307 _106676 _106693)). Qed.
Lemma lem4447310 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4447311 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s)) = (term39 _106676 _106693 k s).
Proof. exact (@lem4447310 ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s))). Qed.
Lemma lem4447312 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term39 _106676 _106693 k s) = ((term25 _106676 _106693 k s) = (term37 _106676 _106693 k s)).
Proof. exact (SYM (@lem4447311 _106676 _106693 k s)). Qed.
Lemma lem4447313 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term40 _106676 _106693 k s) : term40 _106676 _106693 k s.
Proof. exact (h1). Qed.
Lemma lem4447316 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term18 _106676 _106693 s i x) = (term18 _106676 _106693 s i x).
Proof. exact (eq_refl (term18 _106676 _106693 s i x)). Qed.
Lemma lem4447319 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term54 _106676 _106693 s i x) = (s i x).
Proof. exact (@lem16933 (s i x)). Qed.
Lemma lem4447320 {_106676 : Type'} (P : _106676 -> Prop) : (term55 _106676 P) = (term56 _106676 P).
Proof. exact (@lem18392 _106676 P). Qed.
Lemma lem4447321 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term57 _106676 _106693 s i) = (term58 _106676 _106693 s i).
Proof. exact (@lem4447320 _106676 (term20 _106676 _106693 s i)). Qed.
Lemma lem4447322 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term59 _106676 _106693 s i x) = (term18 _106676 _106693 s i x).
Proof. exact (eq_refl (term59 _106676 _106693 s i x)). Qed.
Lemma lem4447323 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4447324 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term60 _106676 _106693 s i x) = (term54 _106676 _106693 s i x).
Proof. exact (MK_COMB (@lem4447323) (@lem4447322 _106676 _106693 s i x)). Qed.
Lemma lem4447325 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term60 _106676 _106693 s i x) = (s i x).
Proof. exact (TRANS (@lem4447324 _106676 _106693 s i x) (@lem4447319 _106676 _106693 s i x)). Qed.
Lemma lem4447326 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term61 _106676 _106693 s i) = (term62 _106676 _106693 s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447325 _106676 _106693 s i x)). Qed.
Lemma lem4447327 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447328 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term58 _106676 _106693 s i) = (term63 _106676 _106693 s i).
Proof. exact (MK_COMB (@lem4447327 _106676) (@lem4447326 _106676 _106693 s i)). Qed.
Lemma lem4447329 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term57 _106676 _106693 s i) = (term63 _106676 _106693 s i).
Proof. exact (TRANS (@lem4447321 _106676 _106693 s i) (@lem4447328 _106676 _106693 s i)). Qed.
Lemma lem4447330 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term20 _106676 _106693 s i) = (term20 _106676 _106693 s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447316 _106676 _106693 s i x)). Qed.
Lemma lem4447331 {_106676 : Type'} : (@all _106676) = (@all _106676).
Proof. exact (eq_refl (@all _106676)). Qed.
Lemma lem4447332 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term21 _106676 _106693 s i) = (term21 _106676 _106693 s i).
Proof. exact (MK_COMB (@lem4447331 _106676) (@lem4447330 _106676 _106693 s i)). Qed.
Lemma lem4447334 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term64 _106693 k i) = (term64 _106693 k i).
Proof. exact (eq_refl (term64 _106693 k i)). Qed.
Lemma lem4447335 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term65 _106676 _106693 k s i) = (term66 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447334 _106693 k i) (@lem4447329 _106676 _106693 s i)). Qed.
Lemma lem4447336 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term67 _106676 _106693 k s i) = (term65 _106676 _106693 k s i).
Proof. exact (@lem17045 (k i) (term21 _106676 _106693 s i)). Qed.
Lemma lem4447337 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term67 _106676 _106693 k s i) = (term66 _106676 _106693 k s i).
Proof. exact (TRANS (@lem4447336 _106676 _106693 k s i) (@lem4447335 _106676 _106693 k s i)). Qed.
Lemma lem4447339 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term14 _106693 k i) = (term14 _106693 k i).
Proof. exact (eq_refl (term14 _106693 k i)). Qed.
Lemma lem4447340 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term22 _106676 _106693 k s i) = (term22 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447339 _106693 k i) (@lem4447332 _106676 _106693 s i)). Qed.
Lemma lem4447341 {_106693 : Type'} (P : _106693 -> Prop) : (term68 _106693 P) = (term69 _106693 P).
Proof. exact (@lem18394 _106693 P). Qed.
Lemma lem4447342 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term25 _106676 _106693 k s) = (term70 _106676 _106693 k s).
Proof. exact (@lem4447341 _106693 (term23 _106676 _106693 k s)). Qed.
Lemma lem4447343 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term71 _106676 _106693 k s i) = (term22 _106676 _106693 k s i).
Proof. exact (eq_refl (term71 _106676 _106693 k s i)). Qed.
Lemma lem4447344 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4447345 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term72 _106676 _106693 k s i) = (term67 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447344) (@lem4447343 _106676 _106693 k s i)). Qed.
Lemma lem4447346 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term72 _106676 _106693 k s i) = (term66 _106676 _106693 k s i).
Proof. exact (TRANS (@lem4447345 _106676 _106693 k s i) (@lem4447337 _106676 _106693 k s i)). Qed.
Lemma lem4447347 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term73 _106676 _106693 k s) = (term74 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447346 _106676 _106693 k s i)). Qed.
Lemma lem4447348 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4447349 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term70 _106676 _106693 k s) = (term75 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447348 _106693) (@lem4447347 _106676 _106693 k s)). Qed.
Lemma lem4447350 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term25 _106676 _106693 k s) = (term75 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447342 _106676 _106693 k s) (@lem4447349 _106676 _106693 k s)). Qed.
Lemma lem4447351 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term23 _106676 _106693 k s) = (term23 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447340 _106676 _106693 k s i)). Qed.
Lemma lem4447352 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447353 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term24 _106676 _106693 k s) = (term24 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447352 _106693) (@lem4447351 _106676 _106693 k s)). Qed.
Lemma lem4447354 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term76 _106676 _106693 k s) = (term24 _106676 _106693 k s).
Proof. exact (@lem16933 (term24 _106676 _106693 k s)). Qed.
Lemma lem4447355 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term76 _106676 _106693 k s) = (term24 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447354 _106676 _106693 k s) (@lem4447353 _106676 _106693 k s)). Qed.
Lemma lem4447364 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term77 _106676 _106693 k s i x) = (term78 _106676 _106693 k s i x).
Proof. exact (@lem17362 (k i) (s i x)). Qed.
Lemma lem4447369 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term30 _106676 _106693 k s i x) = (term79 _106676 _106693 k s i x).
Proof. exact (@lem17265 (k i) (s i x)). Qed.
Lemma lem4447370 {_106676 : Type'} (P : _106676 -> Prop) : (term68 _106676 P) = (term69 _106676 P).
Proof. exact (@lem18394 _106676 P). Qed.
Lemma lem4447371 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term80 _106676 _106693 k s i) = (term81 _106676 _106693 k s i).
Proof. exact (@lem4447370 _106676 (term32 _106676 _106693 k s i)). Qed.
Lemma lem4447372 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term82 _106676 _106693 k s i x) = (term30 _106676 _106693 k s i x).
Proof. exact (eq_refl (term82 _106676 _106693 k s i x)). Qed.
Lemma lem4447373 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4447374 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term83 _106676 _106693 k s i x) = (term77 _106676 _106693 k s i x).
Proof. exact (MK_COMB (@lem4447373) (@lem4447372 _106676 _106693 k s i x)). Qed.
Lemma lem4447375 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term83 _106676 _106693 k s i x) = (term78 _106676 _106693 k s i x).
Proof. exact (TRANS (@lem4447374 _106676 _106693 k s i x) (@lem4447364 _106676 _106693 k s i x)). Qed.
Lemma lem4447376 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term84 _106676 _106693 k s i) = (term85 _106676 _106693 k s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447375 _106676 _106693 k s i x)). Qed.
Lemma lem4447377 {_106676 : Type'} : (@all _106676) = (@all _106676).
Proof. exact (eq_refl (@all _106676)). Qed.
Lemma lem4447378 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term81 _106676 _106693 k s i) = (term86 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447377 _106676) (@lem4447376 _106676 _106693 k s i)). Qed.
Lemma lem4447379 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term80 _106676 _106693 k s i) = (term86 _106676 _106693 k s i).
Proof. exact (TRANS (@lem4447371 _106676 _106693 k s i) (@lem4447378 _106676 _106693 k s i)). Qed.
Lemma lem4447380 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term32 _106676 _106693 k s i) = (term87 _106676 _106693 k s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447369 _106676 _106693 k s i x)). Qed.
Lemma lem4447381 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447382 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term34 _106676 _106693 k s i) = (term88 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447381 _106676) (@lem4447380 _106676 _106693 k s i)). Qed.
Lemma lem4447383 {_106693 : Type'} (P : _106693 -> Prop) : (term55 _106693 P) = (term56 _106693 P).
Proof. exact (@lem18392 _106693 P). Qed.
Lemma lem4447384 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term89 _106676 _106693 k s) = (term90 _106676 _106693 k s).
Proof. exact (@lem4447383 _106693 (term36 _106676 _106693 k s)). Qed.
Lemma lem4447385 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term91 _106676 _106693 k s i) = (term34 _106676 _106693 k s i).
Proof. exact (eq_refl (term91 _106676 _106693 k s i)). Qed.
Lemma lem4447386 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4447387 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term92 _106676 _106693 k s i) = (term80 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447386) (@lem4447385 _106676 _106693 k s i)). Qed.
Lemma lem4447388 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term92 _106676 _106693 k s i) = (term86 _106676 _106693 k s i).
Proof. exact (TRANS (@lem4447387 _106676 _106693 k s i) (@lem4447379 _106676 _106693 k s i)). Qed.
Lemma lem4447389 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term93 _106676 _106693 k s) = (term94 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447388 _106676 _106693 k s i)). Qed.
Lemma lem4447390 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447391 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term90 _106676 _106693 k s) = (term95 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447390 _106693) (@lem4447389 _106676 _106693 k s)). Qed.
Lemma lem4447392 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term89 _106676 _106693 k s) = (term95 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447384 _106676 _106693 k s) (@lem4447391 _106676 _106693 k s)). Qed.
Lemma lem4447393 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term36 _106676 _106693 k s) = (term96 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447382 _106676 _106693 k s i)). Qed.
Lemma lem4447394 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4447395 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term37 _106676 _106693 k s) = (term97 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447394 _106693) (@lem4447393 _106676 _106693 k s)). Qed.
Lemma lem4447396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4447397 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term98 _106676 _106693 k s) = (term99 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447396) (@lem4447355 _106676 _106693 k s)). Qed.
Lemma lem4447398 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term100 _106676 _106693 k s) = (term101 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447397 _106676 _106693 k s) (@lem4447395 _106676 _106693 k s)). Qed.
Lemma lem4447399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4447400 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term102 _106676 _106693 k s) = (term103 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447399) (@lem4447350 _106676 _106693 k s)). Qed.
Lemma lem4447401 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term104 _106676 _106693 k s) = (term105 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447400 _106676 _106693 k s) (@lem4447392 _106676 _106693 k s)). Qed.
Lemma lem4447402 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4447403 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term106 _106676 _106693 k s) = (term107 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447402) (@lem4447401 _106676 _106693 k s)). Qed.
Lemma lem4447404 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term108 _106676 _106693 k s) = (term109 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447403 _106676 _106693 k s) (@lem4447398 _106676 _106693 k s)). Qed.
Lemma lem4447405 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term40 _106676 _106693 k s) = (term108 _106676 _106693 k s).
Proof. exact (@lem17646 (term25 _106676 _106693 k s) (term37 _106676 _106693 k s)). Qed.
Lemma lem4447406 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term40 _106676 _106693 k s) = (term109 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447405 _106676 _106693 k s) (@lem4447404 _106676 _106693 k s)). Qed.
Lemma lem4447464 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4447465 {_106676 : Type'} (P : _106676 -> Prop) (Q : _106676 -> Prop) : (term110 _106676 P Q) = (term111 _106676 P Q).
Proof. exact (@lem4447464 _106676 P Q). Qed.
Lemma lem4447466 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term112 _106676 _106693 k s i) = (term113 _106676 _106693 k s i).
Proof. exact (@lem4447465 _106676 (term114 _106676 _106693 k i) (term20 _106676 _106693 s i)). Qed.
Lemma lem4447467 {_106676 _106693 : Type'} (x : _106676) (k : _106693 -> Prop) (i : _106693) : (term115 _106676 _106693 k i x) = (k i).
Proof. exact (eq_refl (term115 _106676 _106693 k i x)). Qed.
Lemma lem4447468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4447469 {_106676 _106693 : Type'} (x : _106676) (k : _106693 -> Prop) (i : _106693) : (term116 _106676 _106693 k i x) = (term14 _106693 k i).
Proof. exact (MK_COMB (@lem4447468) (@lem4447467 _106676 _106693 x k i)). Qed.
Lemma lem4447470 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term59 _106676 _106693 s i x) = (term18 _106676 _106693 s i x).
Proof. exact (eq_refl (term59 _106676 _106693 s i x)). Qed.
Lemma lem4447471 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term117 _106676 _106693 k s i x) = (term78 _106676 _106693 k s i x).
Proof. exact (MK_COMB (@lem4447469 _106676 _106693 x k i) (@lem4447470 _106676 _106693 s i x)). Qed.
Lemma lem4447472 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term118 _106676 _106693 k s i) = (term85 _106676 _106693 k s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447471 _106676 _106693 k s i x)). Qed.
Lemma lem4447473 {_106676 : Type'} : (@all _106676) = (@all _106676).
Proof. exact (eq_refl (@all _106676)). Qed.
Lemma lem4447474 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term112 _106676 _106693 k s i) = (term86 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447473 _106676) (@lem4447472 _106676 _106693 k s i)). Qed.
Lemma lem4447475 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447476 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term119 _106676 _106693 k s i) = (term120 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447475) (@lem4447474 _106676 _106693 k s i)). Qed.
Lemma lem4447477 {_106676 _106693 : Type'} (x : _106676) (k : _106693 -> Prop) (i : _106693) : (term115 _106676 _106693 k i x) = (k i).
Proof. exact (eq_refl (term115 _106676 _106693 k i x)). Qed.
Lemma lem4447478 {_106676 _106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term121 _106676 _106693 k i) = (term114 _106676 _106693 k i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447477 _106676 _106693 x k i)). Qed.
Lemma lem4447479 {_106676 : Type'} : (@all _106676) = (@all _106676).
Proof. exact (eq_refl (@all _106676)). Qed.
Lemma lem4447480 {_106676 _106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term122 _106676 _106693 k i) = (term123 _106676 _106693 k i).
Proof. exact (MK_COMB (@lem4447479 _106676) (@lem4447478 _106676 _106693 k i)). Qed.
Lemma lem4447481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4447482 {_106676 _106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term124 _106676 _106693 k i) = (term125 _106676 _106693 k i).
Proof. exact (MK_COMB (@lem4447481) (@lem4447480 _106676 _106693 k i)). Qed.
Lemma lem4447483 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term59 _106676 _106693 s i x) = (term18 _106676 _106693 s i x).
Proof. exact (eq_refl (term59 _106676 _106693 s i x)). Qed.
Lemma lem4447484 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term126 _106676 _106693 s i) = (term20 _106676 _106693 s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447483 _106676 _106693 s i x)). Qed.
Lemma lem4447485 {_106676 : Type'} : (@all _106676) = (@all _106676).
Proof. exact (eq_refl (@all _106676)). Qed.
Lemma lem4447486 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term127 _106676 _106693 s i) = (term21 _106676 _106693 s i).
Proof. exact (MK_COMB (@lem4447485 _106676) (@lem4447484 _106676 _106693 s i)). Qed.
Lemma lem4447487 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term113 _106676 _106693 k s i) = (term128 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447482 _106676 _106693 k i) (@lem4447486 _106676 _106693 s i)). Qed.
Lemma lem4447488 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : ((term112 _106676 _106693 k s i) = (term113 _106676 _106693 k s i)) = ((term86 _106676 _106693 k s i) = (term128 _106676 _106693 k s i)).
Proof. exact (MK_COMB (@lem4447476 _106676 _106693 k s i) (@lem4447487 _106676 _106693 k s i)). Qed.
Lemma lem4447489 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term86 _106676 _106693 k s i) = (term128 _106676 _106693 k s i).
Proof. exact (EQ_MP (@lem4447488 _106676 _106693 k s i) (@lem4447466 _106676 _106693 k s i)). Qed.
Lemma lem4447491 {A : Type'} (t : Prop) : (term129 A t) = t.
Proof. exact (EQ_MP (@lem18935 A t) (@lem18934 A t)). Qed.
Lemma lem4447492 {_106676 : Type'} (t : Prop) : (term129 _106676 t) = t.
Proof. exact (@lem4447491 _106676 t). Qed.
Lemma lem4447493 {_106676 _106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term123 _106676 _106693 k i) = (k i).
Proof. exact (@lem4447492 _106676 (k i)). Qed.
Lemma lem4447494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4447495 {_106676 _106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term125 _106676 _106693 k i) = (term14 _106693 k i).
Proof. exact (MK_COMB (@lem4447494) (@lem4447493 _106676 _106693 k i)). Qed.
Lemma lem4447500 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term21 _106676 _106693 s i) = (term21 _106676 _106693 s i).
Proof. exact (eq_refl (term21 _106676 _106693 s i)). Qed.
Lemma lem4447501 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term128 _106676 _106693 k s i) = (term22 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447495 _106676 _106693 k i) (@lem4447500 _106676 _106693 s i)). Qed.
Lemma lem4447502 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term86 _106676 _106693 k s i) = (term22 _106676 _106693 k s i).
Proof. exact (TRANS (@lem4447489 _106676 _106693 k s i) (@lem4447501 _106676 _106693 k s i)). Qed.
Lemma lem4447503 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term94 _106676 _106693 k s) = (term23 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447502 _106676 _106693 k s i)). Qed.
Lemma lem4447504 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447505 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term95 _106676 _106693 k s) = (term24 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447504 _106693) (@lem4447503 _106676 _106693 k s)). Qed.
Lemma lem4447534 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term103 _106676 _106693 k s) = (term103 _106676 _106693 k s).
Proof. exact (eq_refl (term103 _106676 _106693 k s)). Qed.
Lemma lem4447535 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term105 _106676 _106693 k s) = (term130 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447534 _106676 _106693 k s) (@lem4447505 _106676 _106693 k s)). Qed.
Lemma lem4447536 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4447537 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term107 _106676 _106693 k s) = (term131 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447536) (@lem4447535 _106676 _106693 k s)). Qed.
Lemma lem4447575 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4447576 {_106676 : Type'} (P : _106676 -> Prop) (Q : _106676 -> Prop) : (term132 _106676 P Q) = (term133 _106676 P Q).
Proof. exact (@lem4447575 _106676 P Q). Qed.
Lemma lem4447577 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term134 _106676 _106693 k s i) = (term135 _106676 _106693 k s i).
Proof. exact (@lem4447576 _106676 (term136 _106676 _106693 k i) (term62 _106676 _106693 s i)). Qed.
Lemma lem4447578 {_106676 _106693 : Type'} (x : _106676) (k : _106693 -> Prop) (i : _106693) : (term137 _106676 _106693 k i x) = (term138 _106693 k i).
Proof. exact (eq_refl (term137 _106676 _106693 k i x)). Qed.
Lemma lem4447579 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4447580 {_106676 _106693 : Type'} (x : _106676) (k : _106693 -> Prop) (i : _106693) : (term139 _106676 _106693 k i x) = (term64 _106693 k i).
Proof. exact (MK_COMB (@lem4447579) (@lem4447578 _106676 _106693 x k i)). Qed.
Lemma lem4447581 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term140 _106676 _106693 s i x) = (s i x).
Proof. exact (eq_refl (term140 _106676 _106693 s i x)). Qed.
Lemma lem4447582 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term141 _106676 _106693 k s i x) = (term79 _106676 _106693 k s i x).
Proof. exact (MK_COMB (@lem4447580 _106676 _106693 x k i) (@lem4447581 _106676 _106693 s i x)). Qed.
Lemma lem4447583 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term142 _106676 _106693 k s i) = (term87 _106676 _106693 k s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447582 _106676 _106693 k s i x)). Qed.
Lemma lem4447584 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447585 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term134 _106676 _106693 k s i) = (term88 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447584 _106676) (@lem4447583 _106676 _106693 k s i)). Qed.
Lemma lem4447586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447587 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term143 _106676 _106693 k s i) = (term144 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447586) (@lem4447585 _106676 _106693 k s i)). Qed.
Lemma lem4447588 {_106676 _106693 : Type'} (x : _106676) (k : _106693 -> Prop) (i : _106693) : (term137 _106676 _106693 k i x) = (term138 _106693 k i).
Proof. exact (eq_refl (term137 _106676 _106693 k i x)). Qed.
Lemma lem4447589 {_106676 _106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term145 _106676 _106693 k i) = (term136 _106676 _106693 k i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447588 _106676 _106693 x k i)). Qed.
Lemma lem4447590 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447591 {_106676 _106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term146 _106676 _106693 k i) = (term147 _106676 _106693 k i).
Proof. exact (MK_COMB (@lem4447590 _106676) (@lem4447589 _106676 _106693 k i)). Qed.
Lemma lem4447592 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4447593 {_106676 _106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term148 _106676 _106693 k i) = (term149 _106676 _106693 k i).
Proof. exact (MK_COMB (@lem4447592) (@lem4447591 _106676 _106693 k i)). Qed.
Lemma lem4447594 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term140 _106676 _106693 s i x) = (s i x).
Proof. exact (eq_refl (term140 _106676 _106693 s i x)). Qed.
Lemma lem4447595 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term150 _106676 _106693 s i) = (term62 _106676 _106693 s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447594 _106676 _106693 s i x)). Qed.
Lemma lem4447596 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447597 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term151 _106676 _106693 s i) = (term63 _106676 _106693 s i).
Proof. exact (MK_COMB (@lem4447596 _106676) (@lem4447595 _106676 _106693 s i)). Qed.
Lemma lem4447598 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term135 _106676 _106693 k s i) = (term152 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447593 _106676 _106693 k i) (@lem4447597 _106676 _106693 s i)). Qed.
Lemma lem4447599 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : ((term134 _106676 _106693 k s i) = (term135 _106676 _106693 k s i)) = ((term88 _106676 _106693 k s i) = (term152 _106676 _106693 k s i)).
Proof. exact (MK_COMB (@lem4447587 _106676 _106693 k s i) (@lem4447598 _106676 _106693 k s i)). Qed.
Lemma lem4447600 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term88 _106676 _106693 k s i) = (term152 _106676 _106693 k s i).
Proof. exact (EQ_MP (@lem4447599 _106676 _106693 k s i) (@lem4447577 _106676 _106693 k s i)). Qed.
Lemma lem4447602 {A : Type'} (t : Prop) : (term153 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem4447603 {_106676 : Type'} (t : Prop) : (term153 _106676 t) = t.
Proof. exact (@lem4447602 _106676 t). Qed.
Lemma lem4447604 {_106676 _106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term147 _106676 _106693 k i) = (term138 _106693 k i).
Proof. exact (@lem4447603 _106676 (term138 _106693 k i)). Qed.
Lemma lem4447605 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4447606 {_106676 _106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term149 _106676 _106693 k i) = (term64 _106693 k i).
Proof. exact (MK_COMB (@lem4447605) (@lem4447604 _106676 _106693 k i)). Qed.
Lemma lem4447611 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term63 _106676 _106693 s i) = (term63 _106676 _106693 s i).
Proof. exact (eq_refl (term63 _106676 _106693 s i)). Qed.
Lemma lem4447612 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term152 _106676 _106693 k s i) = (term66 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447606 _106676 _106693 k i) (@lem4447611 _106676 _106693 s i)). Qed.
Lemma lem4447613 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term88 _106676 _106693 k s i) = (term66 _106676 _106693 k s i).
Proof. exact (TRANS (@lem4447600 _106676 _106693 k s i) (@lem4447612 _106676 _106693 k s i)). Qed.
Lemma lem4447614 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term96 _106676 _106693 k s) = (term74 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447613 _106676 _106693 k s i)). Qed.
Lemma lem4447615 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4447616 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term97 _106676 _106693 k s) = (term75 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447615 _106693) (@lem4447614 _106676 _106693 k s)). Qed.
Lemma lem4447665 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term99 _106676 _106693 k s) = (term99 _106676 _106693 k s).
Proof. exact (eq_refl (term99 _106676 _106693 k s)). Qed.
Lemma lem4447666 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term101 _106676 _106693 k s) = (term154 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447665 _106676 _106693 k s) (@lem4447616 _106676 _106693 k s)). Qed.
Lemma lem4447667 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term109 _106676 _106693 k s) = (term155 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447537 _106676 _106693 k s) (@lem4447666 _106676 _106693 k s)). Qed.
Lemma lem4447669 {A : Type'} (P : Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4447670 {_106676 : Type'} (P : Prop) (Q : _106676 -> Prop) : (term156 _106676 P Q) = (term157 _106676 P Q).
Proof. exact (@lem4447669 _106676 P Q). Qed.
Lemma lem4447671 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term158 _106676 _106693 k s i) = (term159 _106676 _106693 k s i).
Proof. exact (@lem4447670 _106676 (term138 _106693 k i) (term62 _106676 _106693 s i)). Qed.
Lemma lem4447672 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term140 _106676 _106693 s i x) = (s i x).
Proof. exact (eq_refl (term140 _106676 _106693 s i x)). Qed.
Lemma lem4447673 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term150 _106676 _106693 s i) = (term62 _106676 _106693 s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447672 _106676 _106693 s i x)). Qed.
Lemma lem4447674 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447675 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term151 _106676 _106693 s i) = (term63 _106676 _106693 s i).
Proof. exact (MK_COMB (@lem4447674 _106676) (@lem4447673 _106676 _106693 s i)). Qed.
Lemma lem4447676 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term64 _106693 k i) = (term64 _106693 k i).
Proof. exact (eq_refl (term64 _106693 k i)). Qed.
Lemma lem4447677 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term158 _106676 _106693 k s i) = (term66 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447676 _106693 k i) (@lem4447675 _106676 _106693 s i)). Qed.
Lemma lem4447678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447679 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term160 _106676 _106693 k s i) = (term161 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447678) (@lem4447677 _106676 _106693 k s i)). Qed.
Lemma lem4447680 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term140 _106676 _106693 s i x) = (s i x).
Proof. exact (eq_refl (term140 _106676 _106693 s i x)). Qed.
Lemma lem4447681 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term64 _106693 k i) = (term64 _106693 k i).
Proof. exact (eq_refl (term64 _106693 k i)). Qed.
Lemma lem4447682 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term162 _106676 _106693 k s i x) = (term79 _106676 _106693 k s i x).
Proof. exact (MK_COMB (@lem4447681 _106693 k i) (@lem4447680 _106676 _106693 s i x)). Qed.
Lemma lem4447683 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term163 _106676 _106693 k s i) = (term87 _106676 _106693 k s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447682 _106676 _106693 k s i x)). Qed.
Lemma lem4447684 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447685 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term159 _106676 _106693 k s i) = (term88 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447684 _106676) (@lem4447683 _106676 _106693 k s i)). Qed.
Lemma lem4447686 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : ((term158 _106676 _106693 k s i) = (term159 _106676 _106693 k s i)) = ((term66 _106676 _106693 k s i) = (term88 _106676 _106693 k s i)).
Proof. exact (MK_COMB (@lem4447679 _106676 _106693 k s i) (@lem4447685 _106676 _106693 k s i)). Qed.
Lemma lem4447687 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term66 _106676 _106693 k s i) = (term88 _106676 _106693 k s i).
Proof. exact (EQ_MP (@lem4447686 _106676 _106693 k s i) (@lem4447671 _106676 _106693 k s i)). Qed.
Lemma lem4447688 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term74 _106676 _106693 k s) = (term96 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447687 _106676 _106693 k s i)). Qed.
Lemma lem4447689 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4447690 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term75 _106676 _106693 k s) = (term97 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447689 _106693) (@lem4447688 _106676 _106693 k s)). Qed.
Lemma lem4447692 {A B : Type'} (P : type1413 A B) : (term164 A B P) = (term165 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4447693 {_106676 _106693 : Type'} (P : type1470 _106676 _106693) : (term166 _106676 _106693 P) = (term167 _106676 _106693 P).
Proof. exact (@lem4447692 _106693 _106676 P). Qed.
Lemma lem4447694 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term168 _106676 _106693 k s) = (term169 _106676 _106693 k s).
Proof. exact (@lem4447693 _106676 _106693 (term170 _106676 _106693 k s)). Qed.
Lemma lem4447695 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term171 _106676 _106693 k s i) = (term87 _106676 _106693 k s i).
Proof. exact (eq_refl (term171 _106676 _106693 k s i)). Qed.
Lemma lem4447696 {_106676 : Type'} (x : _106676) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4447697 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term172 _106676 _106693 k s i x) = (term173 _106676 _106693 k s i x).
Proof. exact (MK_COMB (@lem4447695 _106676 _106693 k s i) (@lem4447696 _106676 x)). Qed.
Lemma lem4447698 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term173 _106676 _106693 k s i x) = (term79 _106676 _106693 k s i x).
Proof. exact (eq_refl (term173 _106676 _106693 k s i x)). Qed.
Lemma lem4447699 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term172 _106676 _106693 k s i x) = (term79 _106676 _106693 k s i x).
Proof. exact (TRANS (@lem4447697 _106676 _106693 k s i x) (@lem4447698 _106676 _106693 k s i x)). Qed.
Lemma lem4447700 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term174 _106676 _106693 k s i) = (term87 _106676 _106693 k s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447699 _106676 _106693 k s i x)). Qed.
Lemma lem4447701 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447702 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term175 _106676 _106693 k s i) = (term88 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447701 _106676) (@lem4447700 _106676 _106693 k s i)). Qed.
Lemma lem4447703 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term176 _106676 _106693 k s) = (term96 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447702 _106676 _106693 k s i)). Qed.
Lemma lem4447704 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4447705 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term168 _106676 _106693 k s) = (term97 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447704 _106693) (@lem4447703 _106676 _106693 k s)). Qed.
Lemma lem4447706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447707 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term177 _106676 _106693 k s) = (term178 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447706) (@lem4447705 _106676 _106693 k s)). Qed.
Lemma lem4447708 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term171 _106676 _106693 k s i) = (term87 _106676 _106693 k s i).
Proof. exact (eq_refl (term171 _106676 _106693 k s i)). Qed.
Lemma lem4447709 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem4447710 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) (i : _106693) : (term179 _106676 _106693 k s x i) = (term180 _106676 _106693 k s x i).
Proof. exact (MK_COMB (@lem4447708 _106676 _106693 k s i) (@lem4447709 _106676 _106693 x i)). Qed.
Lemma lem4447711 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) (i : _106693) : (term180 _106676 _106693 k s x i) = (term181 _106676 _106693 k s x i).
Proof. exact (eq_refl (term180 _106676 _106693 k s x i)). Qed.
Lemma lem4447712 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) (i : _106693) : (term179 _106676 _106693 k s x i) = (term181 _106676 _106693 k s x i).
Proof. exact (TRANS (@lem4447710 _106676 _106693 k s x i) (@lem4447711 _106676 _106693 k s x i)). Qed.
Lemma lem4447713 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term182 _106676 _106693 k s x) = (term183 _106676 _106693 k s x).
Proof. exact (fun_ext (fun i : _106693 => @lem4447712 _106676 _106693 k s x i)). Qed.
Lemma lem4447714 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4447715 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term184 _106676 _106693 k s x) = (term185 _106676 _106693 k s x).
Proof. exact (MK_COMB (@lem4447714 _106693) (@lem4447713 _106676 _106693 k s x)). Qed.
Lemma lem4447716 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term186 _106676 _106693 k s) = (term187 _106676 _106693 k s).
Proof. exact (fun_ext (fun x : _106693 -> _106676 => @lem4447715 _106676 _106693 k s x)). Qed.
Lemma lem4447717 {_106676 _106693 : Type'} : (@ex (_106693 -> _106676)) = (@ex (_106693 -> _106676)).
Proof. exact (eq_refl (@ex (_106693 -> _106676))). Qed.
Lemma lem4447718 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term169 _106676 _106693 k s) = (term188 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447717 _106676 _106693) (@lem4447716 _106676 _106693 k s)). Qed.
Lemma lem4447719 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term168 _106676 _106693 k s) = (term169 _106676 _106693 k s)) = ((term97 _106676 _106693 k s) = (term188 _106676 _106693 k s)).
Proof. exact (MK_COMB (@lem4447707 _106676 _106693 k s) (@lem4447718 _106676 _106693 k s)). Qed.
Lemma lem4447720 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term97 _106676 _106693 k s) = (term188 _106676 _106693 k s).
Proof. exact (EQ_MP (@lem4447719 _106676 _106693 k s) (@lem4447694 _106676 _106693 k s)). Qed.
Lemma lem4447721 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term75 _106676 _106693 k s) = (term188 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447690 _106676 _106693 k s) (@lem4447720 _106676 _106693 k s)). Qed.
Lemma lem4447722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4447723 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term103 _106676 _106693 k s) = (term189 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447722) (@lem4447721 _106676 _106693 k s)). Qed.
Lemma lem4447724 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term24 _106676 _106693 k s) = (term24 _106676 _106693 k s).
Proof. exact (eq_refl (term24 _106676 _106693 k s)). Qed.
Lemma lem4447725 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term130 _106676 _106693 k s) = (term190 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447723 _106676 _106693 k s) (@lem4447724 _106676 _106693 k s)). Qed.
Lemma lem4447727 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4447728 {_106676 _106693 : Type'} (P : type805 _106676 _106693) (Q : Prop) : (term193 _106676 _106693 P Q) = (term194 _106676 _106693 P Q).
Proof. exact (@lem4447727 (_106693 -> _106676) P Q). Qed.
Lemma lem4447729 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term195 _106676 _106693 k s) = (term196 _106676 _106693 k s).
Proof. exact (@lem4447728 _106676 _106693 (term187 _106676 _106693 k s) (term24 _106676 _106693 k s)). Qed.
Lemma lem4447730 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term197 _106676 _106693 k s x) = (term185 _106676 _106693 k s x).
Proof. exact (eq_refl (term197 _106676 _106693 k s x)). Qed.
Lemma lem4447731 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term198 _106676 _106693 k s) = (term187 _106676 _106693 k s).
Proof. exact (fun_ext (fun x : _106693 -> _106676 => @lem4447730 _106676 _106693 k s x)). Qed.
Lemma lem4447732 {_106676 _106693 : Type'} : (@ex (_106693 -> _106676)) = (@ex (_106693 -> _106676)).
Proof. exact (eq_refl (@ex (_106693 -> _106676))). Qed.
Lemma lem4447733 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term199 _106676 _106693 k s) = (term188 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447732 _106676 _106693) (@lem4447731 _106676 _106693 k s)). Qed.
Lemma lem4447734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4447735 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term200 _106676 _106693 k s) = (term189 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447734) (@lem4447733 _106676 _106693 k s)). Qed.
Lemma lem4447736 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term24 _106676 _106693 k s) = (term24 _106676 _106693 k s).
Proof. exact (eq_refl (term24 _106676 _106693 k s)). Qed.
Lemma lem4447737 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term195 _106676 _106693 k s) = (term190 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447735 _106676 _106693 k s) (@lem4447736 _106676 _106693 k s)). Qed.
Lemma lem4447738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447739 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term201 _106676 _106693 k s) = (term202 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447738) (@lem4447737 _106676 _106693 k s)). Qed.
Lemma lem4447740 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term197 _106676 _106693 k s x) = (term185 _106676 _106693 k s x).
Proof. exact (eq_refl (term197 _106676 _106693 k s x)). Qed.
Lemma lem4447741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4447742 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term203 _106676 _106693 k s x) = (term204 _106676 _106693 k s x).
Proof. exact (MK_COMB (@lem4447741) (@lem4447740 _106676 _106693 k s x)). Qed.
Lemma lem4447743 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term24 _106676 _106693 k s) = (term24 _106676 _106693 k s).
Proof. exact (eq_refl (term24 _106676 _106693 k s)). Qed.
Lemma lem4447744 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term205 _106676 _106693 x k s) = (term206 _106676 _106693 x k s).
Proof. exact (MK_COMB (@lem4447742 _106676 _106693 k s x) (@lem4447743 _106676 _106693 k s)). Qed.
Lemma lem4447745 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term207 _106676 _106693 k s) = (term208 _106676 _106693 k s).
Proof. exact (fun_ext (fun x : _106693 -> _106676 => @lem4447744 _106676 _106693 x k s)). Qed.
Lemma lem4447746 {_106676 _106693 : Type'} : (@ex (_106693 -> _106676)) = (@ex (_106693 -> _106676)).
Proof. exact (eq_refl (@ex (_106693 -> _106676))). Qed.
Lemma lem4447747 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term196 _106676 _106693 k s) = (term209 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447746 _106676 _106693) (@lem4447745 _106676 _106693 k s)). Qed.
Lemma lem4447748 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term195 _106676 _106693 k s) = (term196 _106676 _106693 k s)) = ((term190 _106676 _106693 k s) = (term209 _106676 _106693 k s)).
Proof. exact (MK_COMB (@lem4447739 _106676 _106693 k s) (@lem4447747 _106676 _106693 k s)). Qed.
Lemma lem4447749 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term190 _106676 _106693 k s) = (term209 _106676 _106693 k s).
Proof. exact (EQ_MP (@lem4447748 _106676 _106693 k s) (@lem4447729 _106676 _106693 k s)). Qed.
Lemma lem4447751 {A : Type'} (P : Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4447752 {_106693 : Type'} (P : Prop) (Q : _106693 -> Prop) : (term210 _106693 P Q) = (term211 _106693 P Q).
Proof. exact (@lem4447751 _106693 P Q). Qed.
Lemma lem4447753 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term212 _106676 _106693 x k s) = (term213 _106676 _106693 x k s).
Proof. exact (@lem4447752 _106693 (term185 _106676 _106693 k s x) (term23 _106676 _106693 k s)). Qed.
Lemma lem4447754 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term71 _106676 _106693 k s i) = (term22 _106676 _106693 k s i).
Proof. exact (eq_refl (term71 _106676 _106693 k s i)). Qed.
Lemma lem4447755 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term214 _106676 _106693 k s) = (term23 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447754 _106676 _106693 k s i)). Qed.
Lemma lem4447756 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447757 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term215 _106676 _106693 k s) = (term24 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447756 _106693) (@lem4447755 _106676 _106693 k s)). Qed.
Lemma lem4447758 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term204 _106676 _106693 k s x) = (term204 _106676 _106693 k s x).
Proof. exact (eq_refl (term204 _106676 _106693 k s x)). Qed.
Lemma lem4447759 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term212 _106676 _106693 x k s) = (term206 _106676 _106693 x k s).
Proof. exact (MK_COMB (@lem4447758 _106676 _106693 k s x) (@lem4447757 _106676 _106693 k s)). Qed.
Lemma lem4447760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447761 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term216 _106676 _106693 x k s) = (term217 _106676 _106693 x k s).
Proof. exact (MK_COMB (@lem4447760) (@lem4447759 _106676 _106693 x k s)). Qed.
Lemma lem4447762 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term71 _106676 _106693 k s i) = (term22 _106676 _106693 k s i).
Proof. exact (eq_refl (term71 _106676 _106693 k s i)). Qed.
Lemma lem4447763 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term204 _106676 _106693 k s x) = (term204 _106676 _106693 k s x).
Proof. exact (eq_refl (term204 _106676 _106693 k s x)). Qed.
Lemma lem4447764 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term218 _106676 _106693 x k s i) = (term219 _106676 _106693 x k s i).
Proof. exact (MK_COMB (@lem4447763 _106676 _106693 k s x) (@lem4447762 _106676 _106693 k s i)). Qed.
Lemma lem4447765 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term220 _106676 _106693 x k s) = (term221 _106676 _106693 x k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447764 _106676 _106693 x k s i)). Qed.
Lemma lem4447766 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447767 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term213 _106676 _106693 x k s) = (term222 _106676 _106693 x k s).
Proof. exact (MK_COMB (@lem4447766 _106693) (@lem4447765 _106676 _106693 x k s)). Qed.
Lemma lem4447768 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term212 _106676 _106693 x k s) = (term213 _106676 _106693 x k s)) = ((term206 _106676 _106693 x k s) = (term222 _106676 _106693 x k s)).
Proof. exact (MK_COMB (@lem4447761 _106676 _106693 x k s) (@lem4447767 _106676 _106693 x k s)). Qed.
Lemma lem4447769 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term206 _106676 _106693 x k s) = (term222 _106676 _106693 x k s).
Proof. exact (EQ_MP (@lem4447768 _106676 _106693 x k s) (@lem4447753 _106676 _106693 x k s)). Qed.
Lemma lem4447770 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term208 _106676 _106693 k s) = (term223 _106676 _106693 k s).
Proof. exact (fun_ext (fun x : _106693 -> _106676 => @lem4447769 _106676 _106693 x k s)). Qed.
Lemma lem4447771 {_106676 _106693 : Type'} : (@ex (_106693 -> _106676)) = (@ex (_106693 -> _106676)).
Proof. exact (eq_refl (@ex (_106693 -> _106676))). Qed.
Lemma lem4447772 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term209 _106676 _106693 k s) = (term224 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447771 _106676 _106693) (@lem4447770 _106676 _106693 k s)). Qed.
Lemma lem4447773 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term190 _106676 _106693 k s) = (term224 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447749 _106676 _106693 k s) (@lem4447772 _106676 _106693 k s)). Qed.
Lemma lem4447774 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term130 _106676 _106693 k s) = (term224 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447725 _106676 _106693 k s) (@lem4447773 _106676 _106693 k s)). Qed.
Lemma lem4447775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4447776 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term131 _106676 _106693 k s) = (term225 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447775) (@lem4447774 _106676 _106693 k s)). Qed.
Lemma lem4447778 {A : Type'} (P : Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4447779 {_106676 : Type'} (P : Prop) (Q : _106676 -> Prop) : (term156 _106676 P Q) = (term157 _106676 P Q).
Proof. exact (@lem4447778 _106676 P Q). Qed.
Lemma lem4447780 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term158 _106676 _106693 k s i) = (term159 _106676 _106693 k s i).
Proof. exact (@lem4447779 _106676 (term138 _106693 k i) (term62 _106676 _106693 s i)). Qed.
Lemma lem4447781 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term140 _106676 _106693 s i x) = (s i x).
Proof. exact (eq_refl (term140 _106676 _106693 s i x)). Qed.
Lemma lem4447782 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term150 _106676 _106693 s i) = (term62 _106676 _106693 s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447781 _106676 _106693 s i x)). Qed.
Lemma lem4447783 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447784 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term151 _106676 _106693 s i) = (term63 _106676 _106693 s i).
Proof. exact (MK_COMB (@lem4447783 _106676) (@lem4447782 _106676 _106693 s i)). Qed.
Lemma lem4447785 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term64 _106693 k i) = (term64 _106693 k i).
Proof. exact (eq_refl (term64 _106693 k i)). Qed.
Lemma lem4447786 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term158 _106676 _106693 k s i) = (term66 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447785 _106693 k i) (@lem4447784 _106676 _106693 s i)). Qed.
Lemma lem4447787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447788 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term160 _106676 _106693 k s i) = (term161 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447787) (@lem4447786 _106676 _106693 k s i)). Qed.
Lemma lem4447789 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term140 _106676 _106693 s i x) = (s i x).
Proof. exact (eq_refl (term140 _106676 _106693 s i x)). Qed.
Lemma lem4447790 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term64 _106693 k i) = (term64 _106693 k i).
Proof. exact (eq_refl (term64 _106693 k i)). Qed.
Lemma lem4447791 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term162 _106676 _106693 k s i x) = (term79 _106676 _106693 k s i x).
Proof. exact (MK_COMB (@lem4447790 _106693 k i) (@lem4447789 _106676 _106693 s i x)). Qed.
Lemma lem4447792 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term163 _106676 _106693 k s i) = (term87 _106676 _106693 k s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447791 _106676 _106693 k s i x)). Qed.
Lemma lem4447793 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447794 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term159 _106676 _106693 k s i) = (term88 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447793 _106676) (@lem4447792 _106676 _106693 k s i)). Qed.
Lemma lem4447795 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : ((term158 _106676 _106693 k s i) = (term159 _106676 _106693 k s i)) = ((term66 _106676 _106693 k s i) = (term88 _106676 _106693 k s i)).
Proof. exact (MK_COMB (@lem4447788 _106676 _106693 k s i) (@lem4447794 _106676 _106693 k s i)). Qed.
Lemma lem4447796 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term66 _106676 _106693 k s i) = (term88 _106676 _106693 k s i).
Proof. exact (EQ_MP (@lem4447795 _106676 _106693 k s i) (@lem4447780 _106676 _106693 k s i)). Qed.
Lemma lem4447797 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term74 _106676 _106693 k s) = (term96 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447796 _106676 _106693 k s i)). Qed.
Lemma lem4447798 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4447799 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term75 _106676 _106693 k s) = (term97 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447798 _106693) (@lem4447797 _106676 _106693 k s)). Qed.
Lemma lem4447801 {A B : Type'} (P : type1413 A B) : (term164 A B P) = (term165 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4447802 {_106676 _106693 : Type'} (P : type1470 _106676 _106693) : (term166 _106676 _106693 P) = (term167 _106676 _106693 P).
Proof. exact (@lem4447801 _106693 _106676 P). Qed.
Lemma lem4447803 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term168 _106676 _106693 k s) = (term169 _106676 _106693 k s).
Proof. exact (@lem4447802 _106676 _106693 (term170 _106676 _106693 k s)). Qed.
Lemma lem4447804 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term171 _106676 _106693 k s i) = (term87 _106676 _106693 k s i).
Proof. exact (eq_refl (term171 _106676 _106693 k s i)). Qed.
Lemma lem4447805 {_106676 : Type'} (x : _106676) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4447806 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term172 _106676 _106693 k s i x) = (term173 _106676 _106693 k s i x).
Proof. exact (MK_COMB (@lem4447804 _106676 _106693 k s i) (@lem4447805 _106676 x)). Qed.
Lemma lem4447807 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term173 _106676 _106693 k s i x) = (term79 _106676 _106693 k s i x).
Proof. exact (eq_refl (term173 _106676 _106693 k s i x)). Qed.
Lemma lem4447808 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term172 _106676 _106693 k s i x) = (term79 _106676 _106693 k s i x).
Proof. exact (TRANS (@lem4447806 _106676 _106693 k s i x) (@lem4447807 _106676 _106693 k s i x)). Qed.
Lemma lem4447809 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term174 _106676 _106693 k s i) = (term87 _106676 _106693 k s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447808 _106676 _106693 k s i x)). Qed.
Lemma lem4447810 {_106676 : Type'} : (@ex _106676) = (@ex _106676).
Proof. exact (eq_refl (@ex _106676)). Qed.
Lemma lem4447811 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term175 _106676 _106693 k s i) = (term88 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447810 _106676) (@lem4447809 _106676 _106693 k s i)). Qed.
Lemma lem4447812 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term176 _106676 _106693 k s) = (term96 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447811 _106676 _106693 k s i)). Qed.
Lemma lem4447813 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4447814 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term168 _106676 _106693 k s) = (term97 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447813 _106693) (@lem4447812 _106676 _106693 k s)). Qed.
Lemma lem4447815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447816 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term177 _106676 _106693 k s) = (term178 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447815) (@lem4447814 _106676 _106693 k s)). Qed.
Lemma lem4447817 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term171 _106676 _106693 k s i) = (term87 _106676 _106693 k s i).
Proof. exact (eq_refl (term171 _106676 _106693 k s i)). Qed.
Lemma lem4447818 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem4447819 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) (i : _106693) : (term179 _106676 _106693 k s x i) = (term180 _106676 _106693 k s x i).
Proof. exact (MK_COMB (@lem4447817 _106676 _106693 k s i) (@lem4447818 _106676 _106693 x i)). Qed.
Lemma lem4447820 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) (i : _106693) : (term180 _106676 _106693 k s x i) = (term181 _106676 _106693 k s x i).
Proof. exact (eq_refl (term180 _106676 _106693 k s x i)). Qed.
Lemma lem4447821 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) (i : _106693) : (term179 _106676 _106693 k s x i) = (term181 _106676 _106693 k s x i).
Proof. exact (TRANS (@lem4447819 _106676 _106693 k s x i) (@lem4447820 _106676 _106693 k s x i)). Qed.
Lemma lem4447822 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term182 _106676 _106693 k s x) = (term183 _106676 _106693 k s x).
Proof. exact (fun_ext (fun i : _106693 => @lem4447821 _106676 _106693 k s x i)). Qed.
Lemma lem4447823 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4447824 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term184 _106676 _106693 k s x) = (term185 _106676 _106693 k s x).
Proof. exact (MK_COMB (@lem4447823 _106693) (@lem4447822 _106676 _106693 k s x)). Qed.
Lemma lem4447825 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term186 _106676 _106693 k s) = (term187 _106676 _106693 k s).
Proof. exact (fun_ext (fun x : _106693 -> _106676 => @lem4447824 _106676 _106693 k s x)). Qed.
Lemma lem4447826 {_106676 _106693 : Type'} : (@ex (_106693 -> _106676)) = (@ex (_106693 -> _106676)).
Proof. exact (eq_refl (@ex (_106693 -> _106676))). Qed.
Lemma lem4447827 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term169 _106676 _106693 k s) = (term188 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447826 _106676 _106693) (@lem4447825 _106676 _106693 k s)). Qed.
Lemma lem4447828 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term168 _106676 _106693 k s) = (term169 _106676 _106693 k s)) = ((term97 _106676 _106693 k s) = (term188 _106676 _106693 k s)).
Proof. exact (MK_COMB (@lem4447816 _106676 _106693 k s) (@lem4447827 _106676 _106693 k s)). Qed.
Lemma lem4447829 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term97 _106676 _106693 k s) = (term188 _106676 _106693 k s).
Proof. exact (EQ_MP (@lem4447828 _106676 _106693 k s) (@lem4447803 _106676 _106693 k s)). Qed.
Lemma lem4447830 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term75 _106676 _106693 k s) = (term188 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447799 _106676 _106693 k s) (@lem4447829 _106676 _106693 k s)). Qed.
Lemma lem4447831 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term99 _106676 _106693 k s) = (term99 _106676 _106693 k s).
Proof. exact (eq_refl (term99 _106676 _106693 k s)). Qed.
Lemma lem4447832 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term154 _106676 _106693 k s) = (term226 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447831 _106676 _106693 k s) (@lem4447830 _106676 _106693 k s)). Qed.
Lemma lem4447834 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4447835 {_106693 : Type'} (P : _106693 -> Prop) (Q : Prop) : (term191 _106693 P Q) = (term192 _106693 P Q).
Proof. exact (@lem4447834 _106693 P Q). Qed.
Lemma lem4447836 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term227 _106676 _106693 k s) = (term228 _106676 _106693 k s).
Proof. exact (@lem4447835 _106693 (term23 _106676 _106693 k s) (term188 _106676 _106693 k s)). Qed.
Lemma lem4447837 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term71 _106676 _106693 k s i) = (term22 _106676 _106693 k s i).
Proof. exact (eq_refl (term71 _106676 _106693 k s i)). Qed.
Lemma lem4447838 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term214 _106676 _106693 k s) = (term23 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447837 _106676 _106693 k s i)). Qed.
Lemma lem4447839 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447840 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term215 _106676 _106693 k s) = (term24 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447839 _106693) (@lem4447838 _106676 _106693 k s)). Qed.
Lemma lem4447841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4447842 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term229 _106676 _106693 k s) = (term99 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447841) (@lem4447840 _106676 _106693 k s)). Qed.
Lemma lem4447843 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term188 _106676 _106693 k s) = (term188 _106676 _106693 k s).
Proof. exact (eq_refl (term188 _106676 _106693 k s)). Qed.
Lemma lem4447844 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term227 _106676 _106693 k s) = (term226 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447842 _106676 _106693 k s) (@lem4447843 _106676 _106693 k s)). Qed.
Lemma lem4447845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447846 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term230 _106676 _106693 k s) = (term231 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447845) (@lem4447844 _106676 _106693 k s)). Qed.
Lemma lem4447847 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term71 _106676 _106693 k s i) = (term22 _106676 _106693 k s i).
Proof. exact (eq_refl (term71 _106676 _106693 k s i)). Qed.
Lemma lem4447848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4447849 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term232 _106676 _106693 k s i) = (term233 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4447848) (@lem4447847 _106676 _106693 k s i)). Qed.
Lemma lem4447850 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term188 _106676 _106693 k s) = (term188 _106676 _106693 k s).
Proof. exact (eq_refl (term188 _106676 _106693 k s)). Qed.
Lemma lem4447851 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term234 _106676 _106693 i k s) = (term235 _106676 _106693 i k s).
Proof. exact (MK_COMB (@lem4447849 _106676 _106693 k s i) (@lem4447850 _106676 _106693 k s)). Qed.
Lemma lem4447852 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term236 _106676 _106693 k s) = (term237 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447851 _106676 _106693 i k s)). Qed.
Lemma lem4447853 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447854 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term228 _106676 _106693 k s) = (term238 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447853 _106693) (@lem4447852 _106676 _106693 k s)). Qed.
Lemma lem4447855 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term227 _106676 _106693 k s) = (term228 _106676 _106693 k s)) = ((term226 _106676 _106693 k s) = (term238 _106676 _106693 k s)).
Proof. exact (MK_COMB (@lem4447846 _106676 _106693 k s) (@lem4447854 _106676 _106693 k s)). Qed.
Lemma lem4447856 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term226 _106676 _106693 k s) = (term238 _106676 _106693 k s).
Proof. exact (EQ_MP (@lem4447855 _106676 _106693 k s) (@lem4447836 _106676 _106693 k s)). Qed.
Lemma lem4447858 {A : Type'} (P : Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4447859 {_106676 _106693 : Type'} (P : Prop) (Q : type805 _106676 _106693) : (term239 _106676 _106693 P Q) = (term240 _106676 _106693 P Q).
Proof. exact (@lem4447858 (_106693 -> _106676) P Q). Qed.
Lemma lem4447860 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term241 _106676 _106693 i k s) = (term242 _106676 _106693 i k s).
Proof. exact (@lem4447859 _106676 _106693 (term22 _106676 _106693 k s i) (term187 _106676 _106693 k s)). Qed.
Lemma lem4447861 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term197 _106676 _106693 k s x) = (term185 _106676 _106693 k s x).
Proof. exact (eq_refl (term197 _106676 _106693 k s x)). Qed.
Lemma lem4447862 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term198 _106676 _106693 k s) = (term187 _106676 _106693 k s).
Proof. exact (fun_ext (fun x : _106693 -> _106676 => @lem4447861 _106676 _106693 k s x)). Qed.
Lemma lem4447863 {_106676 _106693 : Type'} : (@ex (_106693 -> _106676)) = (@ex (_106693 -> _106676)).
Proof. exact (eq_refl (@ex (_106693 -> _106676))). Qed.
Lemma lem4447864 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term199 _106676 _106693 k s) = (term188 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447863 _106676 _106693) (@lem4447862 _106676 _106693 k s)). Qed.
Lemma lem4447865 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term233 _106676 _106693 k s i) = (term233 _106676 _106693 k s i).
Proof. exact (eq_refl (term233 _106676 _106693 k s i)). Qed.
Lemma lem4447866 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term241 _106676 _106693 i k s) = (term235 _106676 _106693 i k s).
Proof. exact (MK_COMB (@lem4447865 _106676 _106693 k s i) (@lem4447864 _106676 _106693 k s)). Qed.
Lemma lem4447867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447868 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term243 _106676 _106693 i k s) = (term244 _106676 _106693 i k s).
Proof. exact (MK_COMB (@lem4447867) (@lem4447866 _106676 _106693 i k s)). Qed.
Lemma lem4447869 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term197 _106676 _106693 k s x) = (term185 _106676 _106693 k s x).
Proof. exact (eq_refl (term197 _106676 _106693 k s x)). Qed.
Lemma lem4447870 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term233 _106676 _106693 k s i) = (term233 _106676 _106693 k s i).
Proof. exact (eq_refl (term233 _106676 _106693 k s i)). Qed.
Lemma lem4447871 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term245 _106676 _106693 i k s x) = (term246 _106676 _106693 i k s x).
Proof. exact (MK_COMB (@lem4447870 _106676 _106693 k s i) (@lem4447869 _106676 _106693 k s x)). Qed.
Lemma lem4447872 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term247 _106676 _106693 i k s) = (term248 _106676 _106693 i k s).
Proof. exact (fun_ext (fun x : _106693 -> _106676 => @lem4447871 _106676 _106693 i k s x)). Qed.
Lemma lem4447873 {_106676 _106693 : Type'} : (@ex (_106693 -> _106676)) = (@ex (_106693 -> _106676)).
Proof. exact (eq_refl (@ex (_106693 -> _106676))). Qed.
Lemma lem4447874 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term242 _106676 _106693 i k s) = (term249 _106676 _106693 i k s).
Proof. exact (MK_COMB (@lem4447873 _106676 _106693) (@lem4447872 _106676 _106693 i k s)). Qed.
Lemma lem4447875 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term241 _106676 _106693 i k s) = (term242 _106676 _106693 i k s)) = ((term235 _106676 _106693 i k s) = (term249 _106676 _106693 i k s)).
Proof. exact (MK_COMB (@lem4447868 _106676 _106693 i k s) (@lem4447874 _106676 _106693 i k s)). Qed.
Lemma lem4447876 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term235 _106676 _106693 i k s) = (term249 _106676 _106693 i k s).
Proof. exact (EQ_MP (@lem4447875 _106676 _106693 i k s) (@lem4447860 _106676 _106693 i k s)). Qed.
Lemma lem4447877 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term237 _106676 _106693 k s) = (term250 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447876 _106676 _106693 i k s)). Qed.
Lemma lem4447878 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447879 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term238 _106676 _106693 k s) = (term251 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447878 _106693) (@lem4447877 _106676 _106693 k s)). Qed.
Lemma lem4447880 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term226 _106676 _106693 k s) = (term251 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447856 _106676 _106693 k s) (@lem4447879 _106676 _106693 k s)). Qed.
Lemma lem4447881 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term154 _106676 _106693 k s) = (term251 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447832 _106676 _106693 k s) (@lem4447880 _106676 _106693 k s)). Qed.
Lemma lem4447882 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term155 _106676 _106693 k s) = (term252 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447776 _106676 _106693 k s) (@lem4447881 _106676 _106693 k s)). Qed.
Lemma lem4447886 {A : Type'} (P : A -> Prop) (Q : Prop) : (term253 A P Q) = (term254 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4447887 {_106676 _106693 : Type'} (P : type805 _106676 _106693) (Q : Prop) : (term255 _106676 _106693 P Q) = (term256 _106676 _106693 P Q).
Proof. exact (@lem4447886 (_106693 -> _106676) P Q). Qed.
Lemma lem4447888 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term257 _106676 _106693 k s) = (term258 _106676 _106693 k s).
Proof. exact (@lem4447887 _106676 _106693 (term223 _106676 _106693 k s) (term251 _106676 _106693 k s)). Qed.
Lemma lem4447889 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term259 _106676 _106693 k s x) = (term222 _106676 _106693 x k s).
Proof. exact (eq_refl (term259 _106676 _106693 k s x)). Qed.
Lemma lem4447890 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term260 _106676 _106693 k s) = (term223 _106676 _106693 k s).
Proof. exact (fun_ext (fun x : _106693 -> _106676 => @lem4447889 _106676 _106693 x k s)). Qed.
Lemma lem4447891 {_106676 _106693 : Type'} : (@ex (_106693 -> _106676)) = (@ex (_106693 -> _106676)).
Proof. exact (eq_refl (@ex (_106693 -> _106676))). Qed.
Lemma lem4447892 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term261 _106676 _106693 k s) = (term224 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447891 _106676 _106693) (@lem4447890 _106676 _106693 k s)). Qed.
Lemma lem4447893 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4447894 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term262 _106676 _106693 k s) = (term225 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447893) (@lem4447892 _106676 _106693 k s)). Qed.
Lemma lem4447895 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term251 _106676 _106693 k s) = (term251 _106676 _106693 k s).
Proof. exact (eq_refl (term251 _106676 _106693 k s)). Qed.
Lemma lem4447896 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term257 _106676 _106693 k s) = (term252 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447894 _106676 _106693 k s) (@lem4447895 _106676 _106693 k s)). Qed.
Lemma lem4447897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447898 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term263 _106676 _106693 k s) = (term264 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447897) (@lem4447896 _106676 _106693 k s)). Qed.
Lemma lem4447899 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term259 _106676 _106693 k s x) = (term222 _106676 _106693 x k s).
Proof. exact (eq_refl (term259 _106676 _106693 k s x)). Qed.
Lemma lem4447900 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4447901 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term265 _106676 _106693 k s x) = (term266 _106676 _106693 x k s).
Proof. exact (MK_COMB (@lem4447900) (@lem4447899 _106676 _106693 x k s)). Qed.
Lemma lem4447902 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term251 _106676 _106693 k s) = (term251 _106676 _106693 k s).
Proof. exact (eq_refl (term251 _106676 _106693 k s)). Qed.
Lemma lem4447903 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term267 _106676 _106693 x k s) = (term268 _106676 _106693 x k s).
Proof. exact (MK_COMB (@lem4447901 _106676 _106693 x k s) (@lem4447902 _106676 _106693 k s)). Qed.
Lemma lem4447904 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term269 _106676 _106693 k s) = (term270 _106676 _106693 k s).
Proof. exact (fun_ext (fun x : _106693 -> _106676 => @lem4447903 _106676 _106693 x k s)). Qed.
Lemma lem4447905 {_106676 _106693 : Type'} : (@ex (_106693 -> _106676)) = (@ex (_106693 -> _106676)).
Proof. exact (eq_refl (@ex (_106693 -> _106676))). Qed.
Lemma lem4447906 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term258 _106676 _106693 k s) = (term271 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447905 _106676 _106693) (@lem4447904 _106676 _106693 k s)). Qed.
Lemma lem4447907 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term257 _106676 _106693 k s) = (term258 _106676 _106693 k s)) = ((term252 _106676 _106693 k s) = (term271 _106676 _106693 k s)).
Proof. exact (MK_COMB (@lem4447898 _106676 _106693 k s) (@lem4447906 _106676 _106693 k s)). Qed.
Lemma lem4447908 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term252 _106676 _106693 k s) = (term271 _106676 _106693 k s).
Proof. exact (EQ_MP (@lem4447907 _106676 _106693 k s) (@lem4447888 _106676 _106693 k s)). Qed.
Lemma lem4447910 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term133 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4447911 {_106693 : Type'} (P : _106693 -> Prop) (Q : _106693 -> Prop) : (term133 _106693 P Q) = (term132 _106693 P Q).
Proof. exact (@lem4447910 _106693 P Q). Qed.
Lemma lem4447912 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term272 _106676 _106693 x k s) = (term273 _106676 _106693 x k s).
Proof. exact (@lem4447911 _106693 (term221 _106676 _106693 x k s) (term250 _106676 _106693 k s)). Qed.
Lemma lem4447913 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term274 _106676 _106693 x k s i) = (term219 _106676 _106693 x k s i).
Proof. exact (eq_refl (term274 _106676 _106693 x k s i)). Qed.
Lemma lem4447914 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term275 _106676 _106693 x k s) = (term221 _106676 _106693 x k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447913 _106676 _106693 x k s i)). Qed.
Lemma lem4447915 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447916 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term276 _106676 _106693 x k s) = (term222 _106676 _106693 x k s).
Proof. exact (MK_COMB (@lem4447915 _106693) (@lem4447914 _106676 _106693 x k s)). Qed.
Lemma lem4447917 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4447918 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term277 _106676 _106693 x k s) = (term266 _106676 _106693 x k s).
Proof. exact (MK_COMB (@lem4447917) (@lem4447916 _106676 _106693 x k s)). Qed.
Lemma lem4447919 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term278 _106676 _106693 k s i) = (term249 _106676 _106693 i k s).
Proof. exact (eq_refl (term278 _106676 _106693 k s i)). Qed.
Lemma lem4447920 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term279 _106676 _106693 k s) = (term250 _106676 _106693 k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447919 _106676 _106693 i k s)). Qed.
Lemma lem4447921 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447922 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term280 _106676 _106693 k s) = (term251 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447921 _106693) (@lem4447920 _106676 _106693 k s)). Qed.
Lemma lem4447923 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term272 _106676 _106693 x k s) = (term268 _106676 _106693 x k s).
Proof. exact (MK_COMB (@lem4447918 _106676 _106693 x k s) (@lem4447922 _106676 _106693 k s)). Qed.
Lemma lem4447924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447925 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term281 _106676 _106693 x k s) = (term282 _106676 _106693 x k s).
Proof. exact (MK_COMB (@lem4447924) (@lem4447923 _106676 _106693 x k s)). Qed.
Lemma lem4447926 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term274 _106676 _106693 x k s i) = (term219 _106676 _106693 x k s i).
Proof. exact (eq_refl (term274 _106676 _106693 x k s i)). Qed.
Lemma lem4447927 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4447928 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term283 _106676 _106693 x k s i) = (term284 _106676 _106693 x k s i).
Proof. exact (MK_COMB (@lem4447927) (@lem4447926 _106676 _106693 x k s i)). Qed.
Lemma lem4447929 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term278 _106676 _106693 k s i) = (term249 _106676 _106693 i k s).
Proof. exact (eq_refl (term278 _106676 _106693 k s i)). Qed.
Lemma lem4447930 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term285 _106676 _106693 x k s i) = (term286 _106676 _106693 x i k s).
Proof. exact (MK_COMB (@lem4447928 _106676 _106693 x k s i) (@lem4447929 _106676 _106693 i k s)). Qed.
Lemma lem4447931 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term287 _106676 _106693 x k s) = (term288 _106676 _106693 x k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447930 _106676 _106693 x i k s)). Qed.
Lemma lem4447932 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447933 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term273 _106676 _106693 x k s) = (term289 _106676 _106693 x k s).
Proof. exact (MK_COMB (@lem4447932 _106693) (@lem4447931 _106676 _106693 x k s)). Qed.
Lemma lem4447934 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term272 _106676 _106693 x k s) = (term273 _106676 _106693 x k s)) = ((term268 _106676 _106693 x k s) = (term289 _106676 _106693 x k s)).
Proof. exact (MK_COMB (@lem4447925 _106676 _106693 x k s) (@lem4447933 _106676 _106693 x k s)). Qed.
Lemma lem4447935 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term268 _106676 _106693 x k s) = (term289 _106676 _106693 x k s).
Proof. exact (EQ_MP (@lem4447934 _106676 _106693 x k s) (@lem4447912 _106676 _106693 x k s)). Qed.
Lemma lem4447937 {A : Type'} (P : Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4447938 {_106676 _106693 : Type'} (P : Prop) (Q : type805 _106676 _106693) : (term290 _106676 _106693 P Q) = (term291 _106676 _106693 P Q).
Proof. exact (@lem4447937 (_106693 -> _106676) P Q). Qed.
Lemma lem4447939 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term292 _106676 _106693 x i k s) = (term293 _106676 _106693 x i k s).
Proof. exact (@lem4447938 _106676 _106693 (term219 _106676 _106693 x k s i) (term248 _106676 _106693 i k s)). Qed.
Lemma lem4447940 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term294 _106676 _106693 i k s x) = (term246 _106676 _106693 i k s x).
Proof. exact (eq_refl (term294 _106676 _106693 i k s x)). Qed.
Lemma lem4447941 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term295 _106676 _106693 i k s) = (term248 _106676 _106693 i k s).
Proof. exact (fun_ext (fun x : _106693 -> _106676 => @lem4447940 _106676 _106693 i k s x)). Qed.
Lemma lem4447942 {_106676 _106693 : Type'} : (@ex (_106693 -> _106676)) = (@ex (_106693 -> _106676)).
Proof. exact (eq_refl (@ex (_106693 -> _106676))). Qed.
Lemma lem4447943 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term296 _106676 _106693 i k s) = (term249 _106676 _106693 i k s).
Proof. exact (MK_COMB (@lem4447942 _106676 _106693) (@lem4447941 _106676 _106693 i k s)). Qed.
Lemma lem4447944 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term284 _106676 _106693 x k s i) = (term284 _106676 _106693 x k s i).
Proof. exact (eq_refl (term284 _106676 _106693 x k s i)). Qed.
Lemma lem4447945 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term292 _106676 _106693 x i k s) = (term286 _106676 _106693 x i k s).
Proof. exact (MK_COMB (@lem4447944 _106676 _106693 x k s i) (@lem4447943 _106676 _106693 i k s)). Qed.
Lemma lem4447946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4447947 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term297 _106676 _106693 x i k s) = (term298 _106676 _106693 x i k s).
Proof. exact (MK_COMB (@lem4447946) (@lem4447945 _106676 _106693 x i k s)). Qed.
Lemma lem4447948 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) : (term294 _106676 _106693 i k s x') = (term246 _106676 _106693 i k s x').
Proof. exact (eq_refl (term294 _106676 _106693 i k s x')). Qed.
Lemma lem4447949 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term284 _106676 _106693 x k s i) = (term284 _106676 _106693 x k s i).
Proof. exact (eq_refl (term284 _106676 _106693 x k s i)). Qed.
Lemma lem4447950 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) : (term299 _106676 _106693 x i k s x') = (term300 _106676 _106693 x i k s x').
Proof. exact (MK_COMB (@lem4447949 _106676 _106693 x k s i) (@lem4447948 _106676 _106693 i k s x')). Qed.
Lemma lem4447951 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term301 _106676 _106693 x i k s) = (term302 _106676 _106693 x i k s).
Proof. exact (fun_ext (fun x' : _106693 -> _106676 => @lem4447950 _106676 _106693 x i k s x')). Qed.
Lemma lem4447952 {_106676 _106693 : Type'} : (@ex (_106693 -> _106676)) = (@ex (_106693 -> _106676)).
Proof. exact (eq_refl (@ex (_106693 -> _106676))). Qed.
Lemma lem4447953 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term293 _106676 _106693 x i k s) = (term303 _106676 _106693 x i k s).
Proof. exact (MK_COMB (@lem4447952 _106676 _106693) (@lem4447951 _106676 _106693 x i k s)). Qed.
Lemma lem4447954 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : ((term292 _106676 _106693 x i k s) = (term293 _106676 _106693 x i k s)) = ((term286 _106676 _106693 x i k s) = (term303 _106676 _106693 x i k s)).
Proof. exact (MK_COMB (@lem4447947 _106676 _106693 x i k s) (@lem4447953 _106676 _106693 x i k s)). Qed.
Lemma lem4447955 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term286 _106676 _106693 x i k s) = (term303 _106676 _106693 x i k s).
Proof. exact (EQ_MP (@lem4447954 _106676 _106693 x i k s) (@lem4447939 _106676 _106693 x i k s)). Qed.
Lemma lem4447956 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term288 _106676 _106693 x k s) = (term304 _106676 _106693 x k s).
Proof. exact (fun_ext (fun i : _106693 => @lem4447955 _106676 _106693 x i k s)). Qed.
Lemma lem4447957 {_106693 : Type'} : (@ex _106693) = (@ex _106693).
Proof. exact (eq_refl (@ex _106693)). Qed.
Lemma lem4447958 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term289 _106676 _106693 x k s) = (term305 _106676 _106693 x k s).
Proof. exact (MK_COMB (@lem4447957 _106693) (@lem4447956 _106676 _106693 x k s)). Qed.
Lemma lem4447959 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term268 _106676 _106693 x k s) = (term305 _106676 _106693 x k s).
Proof. exact (TRANS (@lem4447935 _106676 _106693 x k s) (@lem4447958 _106676 _106693 x k s)). Qed.
Lemma lem4447960 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term270 _106676 _106693 k s) = (term306 _106676 _106693 k s).
Proof. exact (fun_ext (fun x : _106693 -> _106676 => @lem4447959 _106676 _106693 x k s)). Qed.
Lemma lem4447961 {_106676 _106693 : Type'} : (@ex (_106693 -> _106676)) = (@ex (_106693 -> _106676)).
Proof. exact (eq_refl (@ex (_106693 -> _106676))). Qed.
Lemma lem4447962 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term271 _106676 _106693 k s) = (term307 _106676 _106693 k s).
Proof. exact (MK_COMB (@lem4447961 _106676 _106693) (@lem4447960 _106676 _106693 k s)). Qed.
Lemma lem4447963 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term252 _106676 _106693 k s) = (term307 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447908 _106676 _106693 k s) (@lem4447962 _106676 _106693 k s)). Qed.
Lemma lem4447964 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term155 _106676 _106693 k s) = (term307 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447882 _106676 _106693 k s) (@lem4447963 _106676 _106693 k s)). Qed.
Lemma lem4447965 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term109 _106676 _106693 k s) = (term307 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447667 _106676 _106693 k s) (@lem4447964 _106676 _106693 k s)). Qed.
Lemma lem4447966 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term40 _106676 _106693 k s) = (term307 _106676 _106693 k s).
Proof. exact (TRANS (@lem4447406 _106676 _106693 k s) (@lem4447965 _106676 _106693 k s)). Qed.
Lemma lem4447967 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term40 _106676 _106693 k s) : term307 _106676 _106693 k s.
Proof. exact (EQ_MP (@lem4447966 _106676 _106693 k s) (@lem4447313 _106676 _106693 k s h1)). Qed.
Lemma lem4447968 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term305 _106676 _106693 x k s) : term305 _106676 _106693 x k s.
Proof. exact (h1). Qed.
Lemma lem4447969 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term303 _106676 _106693 x i k s) : term303 _106676 _106693 x i k s.
Proof. exact (h1). Qed.
Lemma lem4447970 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term300 _106676 _106693 x i k s x') : term300 _106676 _106693 x i k s x'.
Proof. exact (h1). Qed.
Lemma lem4447985 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (i : _106693) : (term181 _106676 _106693 k s x' i) = (term181 _106676 _106693 k s x' i).
Proof. exact (eq_refl (term181 _106676 _106693 k s x' i)). Qed.
Lemma lem4447986 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) : (term183 _106676 _106693 k s x') = (term183 _106676 _106693 k s x').
Proof. exact (fun_ext (fun i : _106693 => @lem4447985 _106676 _106693 k s x' i)). Qed.
Lemma lem4447987 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4447988 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) : (term185 _106676 _106693 k s x') = (term185 _106676 _106693 k s x').
Proof. exact (MK_COMB (@lem4447987 _106693) (@lem4447986 _106676 _106693 k s x')). Qed.
Lemma lem4447995 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term18 _106676 _106693 s i x) = (term18 _106676 _106693 s i x).
Proof. exact (eq_refl (term18 _106676 _106693 s i x)). Qed.
Lemma lem4447996 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term20 _106676 _106693 s i) = (term20 _106676 _106693 s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4447995 _106676 _106693 s i x)). Qed.
Lemma lem4447997 {_106676 : Type'} : (@all _106676) = (@all _106676).
Proof. exact (eq_refl (@all _106676)). Qed.
Lemma lem4447998 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term21 _106676 _106693 s i) = (term21 _106676 _106693 s i).
Proof. exact (MK_COMB (@lem4447997 _106676) (@lem4447996 _106676 _106693 s i)). Qed.
Lemma lem4448003 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term14 _106693 k i) = (term14 _106693 k i).
Proof. exact (eq_refl (term14 _106693 k i)). Qed.
Lemma lem4448004 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term22 _106676 _106693 k s i) = (term22 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4448003 _106693 k i) (@lem4447998 _106676 _106693 s i)). Qed.
Lemma lem4448005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4448006 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term233 _106676 _106693 k s i) = (term233 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4448005) (@lem4448004 _106676 _106693 k s i)). Qed.
Lemma lem4448007 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) : (term246 _106676 _106693 i k s x') = (term246 _106676 _106693 i k s x').
Proof. exact (MK_COMB (@lem4448006 _106676 _106693 k s i) (@lem4447988 _106676 _106693 k s x')). Qed.
Lemma lem4448014 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term18 _106676 _106693 s i x) = (term18 _106676 _106693 s i x).
Proof. exact (eq_refl (term18 _106676 _106693 s i x)). Qed.
Lemma lem4448015 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term20 _106676 _106693 s i) = (term20 _106676 _106693 s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4448014 _106676 _106693 s i x)). Qed.
Lemma lem4448016 {_106676 : Type'} : (@all _106676) = (@all _106676).
Proof. exact (eq_refl (@all _106676)). Qed.
Lemma lem4448017 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term21 _106676 _106693 s i) = (term21 _106676 _106693 s i).
Proof. exact (MK_COMB (@lem4448016 _106676) (@lem4448015 _106676 _106693 s i)). Qed.
Lemma lem4448022 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term14 _106693 k i) = (term14 _106693 k i).
Proof. exact (eq_refl (term14 _106693 k i)). Qed.
Lemma lem4448023 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term22 _106676 _106693 k s i) = (term22 _106676 _106693 k s i).
Proof. exact (MK_COMB (@lem4448022 _106693 k i) (@lem4448017 _106676 _106693 s i)). Qed.
Lemma lem4448038 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) (i : _106693) : (term181 _106676 _106693 k s x i) = (term181 _106676 _106693 k s x i).
Proof. exact (eq_refl (term181 _106676 _106693 k s x i)). Qed.
Lemma lem4448039 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term183 _106676 _106693 k s x) = (term183 _106676 _106693 k s x).
Proof. exact (fun_ext (fun i : _106693 => @lem4448038 _106676 _106693 k s x i)). Qed.
Lemma lem4448040 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4448041 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term185 _106676 _106693 k s x) = (term185 _106676 _106693 k s x).
Proof. exact (MK_COMB (@lem4448040 _106693) (@lem4448039 _106676 _106693 k s x)). Qed.
Lemma lem4448042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4448043 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term204 _106676 _106693 k s x) = (term204 _106676 _106693 k s x).
Proof. exact (MK_COMB (@lem4448042) (@lem4448041 _106676 _106693 k s x)). Qed.
Lemma lem4448044 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term219 _106676 _106693 x k s i) = (term219 _106676 _106693 x k s i).
Proof. exact (MK_COMB (@lem4448043 _106676 _106693 k s x) (@lem4448023 _106676 _106693 k s i)). Qed.
Lemma lem4448045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4448046 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) : (term284 _106676 _106693 x k s i) = (term284 _106676 _106693 x k s i).
Proof. exact (MK_COMB (@lem4448045) (@lem4448044 _106676 _106693 x k s i)). Qed.
Lemma lem4448047 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) : (term300 _106676 _106693 x i k s x') = (term300 _106676 _106693 x i k s x').
Proof. exact (MK_COMB (@lem4448046 _106676 _106693 x k s i) (@lem4448007 _106676 _106693 i k s x')). Qed.
Lemma lem4448048 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term300 _106676 _106693 x i k s x') : term300 _106676 _106693 x i k s x'.
Proof. exact (EQ_MP (@lem4448047 _106676 _106693 x i k s x') (@lem4447970 _106676 _106693 x i k s x' h1)). Qed.
Lemma lem4448049 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term219 _106676 _106693 x k s i.
Proof. exact (h1). Qed.
Lemma lem4448050 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term246 _106676 _106693 i k s x'.
Proof. exact (h1). Qed.
Lemma lem4448051 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term22 _106676 _106693 k s i.
Proof. exact (proj2 (@lem4448049 _106676 _106693 x k s i h1)). Qed.
Lemma lem4448052 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term185 _106676 _106693 k s x.
Proof. exact (proj1 (@lem4448049 _106676 _106693 x k s i h1)). Qed.
Lemma lem4448053 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term21 _106676 _106693 s i.
Proof. exact (proj2 (@lem4448051 _106676 _106693 x k s i h1)). Qed.
Lemma lem4448055 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term185 _106676 _106693 k s x'.
Proof. exact (proj2 (@lem4448050 _106676 _106693 i k s x' h1)). Qed.
Lemma lem4448056 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term22 _106676 _106693 k s i.
Proof. exact (proj1 (@lem4448050 _106676 _106693 i k s x' h1)). Qed.
Lemma lem4448057 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term21 _106676 _106693 s i.
Proof. exact (proj2 (@lem4448056 _106676 _106693 i k s x' h1)). Qed.
Lemma lem4448066 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) (i : _106693) : (term181 _106676 _106693 k s x i) = (term181 _106676 _106693 k s x i).
Proof. exact (eq_refl (term181 _106676 _106693 k s x i)). Qed.
Lemma lem4448067 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term183 _106676 _106693 k s x) = (term183 _106676 _106693 k s x).
Proof. exact (fun_ext (fun i : _106693 => @lem4448066 _106676 _106693 k s x i)). Qed.
Lemma lem4448068 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4448070 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) : (term185 _106676 _106693 k s x) = (term185 _106676 _106693 k s x).
Proof. exact (MK_COMB (@lem4448068 _106693) (@lem4448067 _106676 _106693 k s x)). Qed.
Lemma lem4448071 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term185 _106676 _106693 k s x.
Proof. exact (EQ_MP (@lem4448070 _106676 _106693 k s x) (@lem4448052 _106676 _106693 x k s i h1)). Qed.
Lemma lem4448077 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term18 _106676 _106693 s i x) = (term18 _106676 _106693 s i x).
Proof. exact (eq_refl (term18 _106676 _106693 s i x)). Qed.
Lemma lem4448078 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term20 _106676 _106693 s i) = (term20 _106676 _106693 s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4448077 _106676 _106693 s i x)). Qed.
Lemma lem4448079 {_106676 : Type'} : (@all _106676) = (@all _106676).
Proof. exact (eq_refl (@all _106676)). Qed.
Lemma lem4448081 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term21 _106676 _106693 s i) = (term21 _106676 _106693 s i).
Proof. exact (MK_COMB (@lem4448079 _106676) (@lem4448078 _106676 _106693 s i)). Qed.
Lemma lem4448082 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term21 _106676 _106693 s i.
Proof. exact (EQ_MP (@lem4448081 _106676 _106693 s i) (@lem4448053 _106676 _106693 x k s i h1)). Qed.
Lemma lem4448090 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (i : _106693) : (term181 _106676 _106693 k s x' i) = (term181 _106676 _106693 k s x' i).
Proof. exact (eq_refl (term181 _106676 _106693 k s x' i)). Qed.
Lemma lem4448091 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) : (term183 _106676 _106693 k s x') = (term183 _106676 _106693 k s x').
Proof. exact (fun_ext (fun i : _106693 => @lem4448090 _106676 _106693 k s x' i)). Qed.
Lemma lem4448092 {_106693 : Type'} : (@all _106693) = (@all _106693).
Proof. exact (eq_refl (@all _106693)). Qed.
Lemma lem4448094 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) : (term185 _106676 _106693 k s x') = (term185 _106676 _106693 k s x').
Proof. exact (MK_COMB (@lem4448092 _106693) (@lem4448091 _106676 _106693 k s x')). Qed.
Lemma lem4448095 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term185 _106676 _106693 k s x'.
Proof. exact (EQ_MP (@lem4448094 _106676 _106693 k s x') (@lem4448055 _106676 _106693 i k s x' h1)). Qed.
Lemma lem4448101 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (x : _106676) : (term18 _106676 _106693 s i x) = (term18 _106676 _106693 s i x).
Proof. exact (eq_refl (term18 _106676 _106693 s i x)). Qed.
Lemma lem4448102 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term20 _106676 _106693 s i) = (term20 _106676 _106693 s i).
Proof. exact (fun_ext (fun x : _106676 => @lem4448101 _106676 _106693 s i x)). Qed.
Lemma lem4448103 {_106676 : Type'} : (@all _106676) = (@all _106676).
Proof. exact (eq_refl (@all _106676)). Qed.
Lemma lem4448105 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) : (term21 _106676 _106693 s i) = (term21 _106676 _106693 s i).
Proof. exact (MK_COMB (@lem4448103 _106676) (@lem4448102 _106676 _106693 s i)). Qed.
Lemma lem4448106 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term21 _106676 _106693 s i.
Proof. exact (EQ_MP (@lem4448105 _106676 _106693 s i) (@lem4448057 _106676 _106693 i k s x' h1)). Qed.
Lemma lem4448107 {_106676 _106693 : Type'} (_51388 : _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term308 _106676 _106693 k s x _51388.
Proof. exact (@lem4448071 _106676 _106693 x k s i h1 _51388). Qed.
Lemma lem4448108 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) (_51388 : _106693) : (term308 _106676 _106693 k s x _51388) = (term181 _106676 _106693 k s x _51388).
Proof. exact (eq_refl (term308 _106676 _106693 k s x _51388)). Qed.
Lemma lem4448110 {_106676 _106693 : Type'} (_51389 : _106676) (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term59 _106676 _106693 s i _51389.
Proof. exact (@lem4448082 _106676 _106693 x k s i h1 _51389). Qed.
Lemma lem4448111 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (_51389 : _106676) : (term59 _106676 _106693 s i _51389) = (term18 _106676 _106693 s i _51389).
Proof. exact (eq_refl (term59 _106676 _106693 s i _51389)). Qed.
Lemma lem4448113 {_106676 _106693 : Type'} (_51390 : _106693) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term308 _106676 _106693 k s x' _51390.
Proof. exact (@lem4448095 _106676 _106693 i k s x' h1 _51390). Qed.
Lemma lem4448114 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (_51390 : _106693) : (term308 _106676 _106693 k s x' _51390) = (term181 _106676 _106693 k s x' _51390).
Proof. exact (eq_refl (term308 _106676 _106693 k s x' _51390)). Qed.
Lemma lem4448116 {_106676 _106693 : Type'} (_51391 : _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term59 _106676 _106693 s i _51391.
Proof. exact (@lem4448106 _106676 _106693 i k s x' h1 _51391). Qed.
Lemma lem4448117 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (_51391 : _106676) : (term59 _106676 _106693 s i _51391) = (term18 _106676 _106693 s i _51391).
Proof. exact (eq_refl (term59 _106676 _106693 s i _51391)). Qed.
Lemma lem4448124 {_106676 _106693 : Type'} (_51388 : _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term181 _106676 _106693 k s x _51388.
Proof. exact (EQ_MP (@lem4448108 _106676 _106693 k s x _51388) (@lem4448107 _106676 _106693 _51388 x k s i h1)). Qed.
Lemma lem4448128 {_106676 _106693 : Type'} (_51389 : _106676) (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term18 _106676 _106693 s i _51389.
Proof. exact (EQ_MP (@lem4448111 _106676 _106693 s i _51389) (@lem4448110 _106676 _106693 _51389 x k s i h1)). Qed.
Lemma lem4448134 {_106676 _106693 : Type'} (_51390 : _106693) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term181 _106676 _106693 k s x' _51390.
Proof. exact (EQ_MP (@lem4448114 _106676 _106693 k s x' _51390) (@lem4448113 _106676 _106693 _51390 i k s x' h1)). Qed.
Lemma lem4448138 {_106676 _106693 : Type'} (_51391 : _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term18 _106676 _106693 s i _51391.
Proof. exact (EQ_MP (@lem4448117 _106676 _106693 s i _51391) (@lem4448116 _106676 _106693 _51391 i k s x' h1)). Qed.
Lemma lem4448140 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : k i.
Proof. exact (proj1 (@lem4448051 _106676 _106693 x k s i h1)). Qed.
Lemma lem4448141 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term309 _106693 k i.
Proof. exact (fun h0 : term138 _106693 k i => @lem4448140 _106676 _106693 x k s i h1). Qed.
Lemma lem4448143 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4448144 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term309 _106693 k i) = (k i).
Proof. exact (@lem4448143 (k i)). Qed.
Lemma lem4448145 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : k i.
Proof. exact (EQ_MP (@lem4448144 _106693 k i) (@lem4448141 _106676 _106693 x k s i h1)). Qed.
Lemma lem4448151 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4448152 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (_51388 : _106693) : (term181 _106676 _106693 k s x _51388) = (term311 _106676 _106693 s x k _51388).
Proof. exact (@lem4448151 (term312 _106676 _106693 s x _51388) (term138 _106693 k _51388)). Qed.
Lemma lem4448158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4448159 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (_51388 : _106693) : (term313 _106676 _106693 k s x _51388) = (term314 _106676 _106693 s x k _51388).
Proof. exact (MK_COMB (@lem4448158) (@lem4448152 _106676 _106693 s x k _51388)). Qed.
Lemma lem4448165 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (_51388 : _106693) : (term311 _106676 _106693 s x k _51388) = (term311 _106676 _106693 s x k _51388).
Proof. exact (eq_refl (term311 _106676 _106693 s x k _51388)). Qed.
Lemma lem4448166 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (_51388 : _106693) : ((term181 _106676 _106693 k s x _51388) = (term311 _106676 _106693 s x k _51388)) = ((term311 _106676 _106693 s x k _51388) = (term311 _106676 _106693 s x k _51388)).
Proof. exact (MK_COMB (@lem4448159 _106676 _106693 s x k _51388) (@lem4448165 _106676 _106693 s x k _51388)). Qed.
Lemma lem4448168 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4448169 (x : Prop) : (x = x) = True.
Proof. exact (@lem4448168 Prop x). Qed.
Lemma lem4448170 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (_51388 : _106693) : ((term311 _106676 _106693 s x k _51388) = (term311 _106676 _106693 s x k _51388)) = True.
Proof. exact (@lem4448169 (term311 _106676 _106693 s x k _51388)). Qed.
Lemma lem4448171 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (_51388 : _106693) : ((term181 _106676 _106693 k s x _51388) = (term311 _106676 _106693 s x k _51388)) = True.
Proof. exact (TRANS (@lem4448166 _106676 _106693 s x k _51388) (@lem4448170 _106676 _106693 s x k _51388)). Qed.
Lemma lem4448172 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (_51388 : _106693) : True = ((term181 _106676 _106693 k s x _51388) = (term311 _106676 _106693 s x k _51388)).
Proof. exact (SYM (@lem4448171 _106676 _106693 s x k _51388)). Qed.
Lemma lem4448173 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (_51388 : _106693) : (term181 _106676 _106693 k s x _51388) = (term311 _106676 _106693 s x k _51388).
Proof. exact (EQ_MP (@lem4448172 _106676 _106693 s x k _51388) (@lem0)). Qed.
Lemma lem4448174 {_106676 _106693 : Type'} (_51388 : _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term311 _106676 _106693 s x k _51388.
Proof. exact (EQ_MP (@lem4448173 _106676 _106693 s x k _51388) (@lem4448124 _106676 _106693 _51388 x k s i h1)). Qed.
Lemma lem4448176 (b : Prop) (a : Prop) : (a \/ b) = (term315 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4448177 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) (_51388 : _106693) : (term311 _106676 _106693 s x k _51388) = (term316 _106676 _106693 k s x _51388).
Proof. exact (@lem4448176 (term138 _106693 k _51388) (term312 _106676 _106693 s x _51388)). Qed.
Lemma lem4448179 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4448180 {_106693 : Type'} (k : _106693 -> Prop) (_51388 : _106693) : (term317 _106693 k _51388) = (k _51388).
Proof. exact (@lem4448179 (k _51388)). Qed.
Lemma lem4448181 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4448182 {_106693 : Type'} (k : _106693 -> Prop) (_51388 : _106693) : (term318 _106693 k _51388) = (term28 _106693 k _51388).
Proof. exact (MK_COMB (@lem4448181) (@lem4448180 _106693 k _51388)). Qed.
Lemma lem4448183 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x : _106693 -> _106676) (_51388 : _106693) : (term312 _106676 _106693 s x _51388) = (term312 _106676 _106693 s x _51388).
Proof. exact (eq_refl (term312 _106676 _106693 s x _51388)). Qed.
Lemma lem4448184 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) (_51388 : _106693) : (term316 _106676 _106693 k s x _51388) = (term319 _106676 _106693 k s x _51388).
Proof. exact (MK_COMB (@lem4448182 _106693 k _51388) (@lem4448183 _106676 _106693 s x _51388)). Qed.
Lemma lem4448185 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x : _106693 -> _106676) (_51388 : _106693) : (term311 _106676 _106693 s x k _51388) = (term319 _106676 _106693 k s x _51388).
Proof. exact (TRANS (@lem4448177 _106676 _106693 k s x _51388) (@lem4448184 _106676 _106693 k s x _51388)). Qed.
Lemma lem4448188 {_106676 _106693 : Type'} (_51388 : _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term319 _106676 _106693 k s x _51388.
Proof. exact (EQ_MP (@lem4448185 _106676 _106693 k s x _51388) (@lem4448174 _106676 _106693 _51388 x k s i h1)). Qed.
Lemma lem4448189 {_106676 _106693 : Type'} (_51388 : _106693) (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term319 _106676 _106693 k s x _51388.
Proof. exact (@lem4448188 _106676 _106693 _51388 x k s i h1). Qed.
Lemma lem4448190 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term319 _106676 _106693 k s x i.
Proof. exact (@lem4448189 _106676 _106693 i x k s i h1). Qed.
Lemma lem4448193 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term312 _106676 _106693 s x i.
Proof. exact (@lem4448190 _106676 _106693 x k s i h1 (@lem4448145 _106676 _106693 x k s i h1)). Qed.
Lemma lem4448194 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term320 _106676 _106693 s x i.
Proof. exact (fun h0 : term321 _106676 _106693 s x i => @lem4448193 _106676 _106693 x k s i h1). Qed.
Lemma lem4448196 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4448197 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x : _106693 -> _106676) (i : _106693) : (term320 _106676 _106693 s x i) = (term312 _106676 _106693 s x i).
Proof. exact (@lem4448196 (term312 _106676 _106693 s x i)). Qed.
Lemma lem4448198 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term312 _106676 _106693 s x i.
Proof. exact (EQ_MP (@lem4448197 _106676 _106693 s x i) (@lem4448194 _106676 _106693 x k s i h1)). Qed.
Lemma lem4448201 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4448203 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (_51389 : _106676) : (term18 _106676 _106693 s i _51389) = (term322 _106676 _106693 s i _51389).
Proof. exact (@lem4448201 (s i _51389)). Qed.
Lemma lem4448206 {_106676 _106693 : Type'} (_51389 : _106676) (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term322 _106676 _106693 s i _51389.
Proof. exact (EQ_MP (@lem4448203 _106676 _106693 s i _51389) (@lem4448128 _106676 _106693 _51389 x k s i h1)). Qed.
Lemma lem4448207 {_106676 _106693 : Type'} (_51389 : _106676) (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term322 _106676 _106693 s i _51389.
Proof. exact (@lem4448206 _106676 _106693 _51389 x k s i h1). Qed.
Lemma lem4448208 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term323 _106676 _106693 s x i.
Proof. exact (@lem4448207 _106676 _106693 (x i) x k s i h1). Qed.
Lemma lem4448211 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : False.
Proof. exact (@lem4448208 _106676 _106693 x k s i h1 (@lem4448198 _106676 _106693 x k s i h1)). Qed.
Lemma lem4448212 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : term324.
Proof. exact (fun h0 : ~ False => @lem4448211 _106676 _106693 x k s i h1). Qed.
Lemma lem4448214 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4448215 : term324 = False.
Proof. exact (@lem4448214 False). Qed.
Lemma lem4448216 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (i : _106693) (h1 : term219 _106676 _106693 x k s i) : False.
Proof. exact (EQ_MP (@lem4448215) (@lem4448212 _106676 _106693 x k s i h1)). Qed.
Lemma lem4448218 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : k i.
Proof. exact (proj1 (@lem4448056 _106676 _106693 i k s x' h1)). Qed.
Lemma lem4448219 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term309 _106693 k i.
Proof. exact (fun h0 : term138 _106693 k i => @lem4448218 _106676 _106693 i k s x' h1). Qed.
Lemma lem4448221 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4448222 {_106693 : Type'} (k : _106693 -> Prop) (i : _106693) : (term309 _106693 k i) = (k i).
Proof. exact (@lem4448221 (k i)). Qed.
Lemma lem4448223 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : k i.
Proof. exact (EQ_MP (@lem4448222 _106693 k i) (@lem4448219 _106676 _106693 i k s x' h1)). Qed.
Lemma lem4448229 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4448230 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (k : _106693 -> Prop) (_51390 : _106693) : (term181 _106676 _106693 k s x' _51390) = (term311 _106676 _106693 s x' k _51390).
Proof. exact (@lem4448229 (term312 _106676 _106693 s x' _51390) (term138 _106693 k _51390)). Qed.
Lemma lem4448236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4448237 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (k : _106693 -> Prop) (_51390 : _106693) : (term313 _106676 _106693 k s x' _51390) = (term314 _106676 _106693 s x' k _51390).
Proof. exact (MK_COMB (@lem4448236) (@lem4448230 _106676 _106693 s x' k _51390)). Qed.
Lemma lem4448243 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (k : _106693 -> Prop) (_51390 : _106693) : (term311 _106676 _106693 s x' k _51390) = (term311 _106676 _106693 s x' k _51390).
Proof. exact (eq_refl (term311 _106676 _106693 s x' k _51390)). Qed.
Lemma lem4448244 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (k : _106693 -> Prop) (_51390 : _106693) : ((term181 _106676 _106693 k s x' _51390) = (term311 _106676 _106693 s x' k _51390)) = ((term311 _106676 _106693 s x' k _51390) = (term311 _106676 _106693 s x' k _51390)).
Proof. exact (MK_COMB (@lem4448237 _106676 _106693 s x' k _51390) (@lem4448243 _106676 _106693 s x' k _51390)). Qed.
Lemma lem4448246 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4448247 (x : Prop) : (x = x) = True.
Proof. exact (@lem4448246 Prop x). Qed.
Lemma lem4448248 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (k : _106693 -> Prop) (_51390 : _106693) : ((term311 _106676 _106693 s x' k _51390) = (term311 _106676 _106693 s x' k _51390)) = True.
Proof. exact (@lem4448247 (term311 _106676 _106693 s x' k _51390)). Qed.
Lemma lem4448249 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (k : _106693 -> Prop) (_51390 : _106693) : ((term181 _106676 _106693 k s x' _51390) = (term311 _106676 _106693 s x' k _51390)) = True.
Proof. exact (TRANS (@lem4448244 _106676 _106693 s x' k _51390) (@lem4448248 _106676 _106693 s x' k _51390)). Qed.
Lemma lem4448250 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (k : _106693 -> Prop) (_51390 : _106693) : True = ((term181 _106676 _106693 k s x' _51390) = (term311 _106676 _106693 s x' k _51390)).
Proof. exact (SYM (@lem4448249 _106676 _106693 s x' k _51390)). Qed.
Lemma lem4448251 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (k : _106693 -> Prop) (_51390 : _106693) : (term181 _106676 _106693 k s x' _51390) = (term311 _106676 _106693 s x' k _51390).
Proof. exact (EQ_MP (@lem4448250 _106676 _106693 s x' k _51390) (@lem0)). Qed.
Lemma lem4448252 {_106676 _106693 : Type'} (_51390 : _106693) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term311 _106676 _106693 s x' k _51390.
Proof. exact (EQ_MP (@lem4448251 _106676 _106693 s x' k _51390) (@lem4448134 _106676 _106693 _51390 i k s x' h1)). Qed.
Lemma lem4448254 (b : Prop) (a : Prop) : (a \/ b) = (term315 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4448255 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (_51390 : _106693) : (term311 _106676 _106693 s x' k _51390) = (term316 _106676 _106693 k s x' _51390).
Proof. exact (@lem4448254 (term138 _106693 k _51390) (term312 _106676 _106693 s x' _51390)). Qed.
Lemma lem4448257 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4448258 {_106693 : Type'} (k : _106693 -> Prop) (_51390 : _106693) : (term317 _106693 k _51390) = (k _51390).
Proof. exact (@lem4448257 (k _51390)). Qed.
Lemma lem4448259 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4448260 {_106693 : Type'} (k : _106693 -> Prop) (_51390 : _106693) : (term318 _106693 k _51390) = (term28 _106693 k _51390).
Proof. exact (MK_COMB (@lem4448259) (@lem4448258 _106693 k _51390)). Qed.
Lemma lem4448261 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (_51390 : _106693) : (term312 _106676 _106693 s x' _51390) = (term312 _106676 _106693 s x' _51390).
Proof. exact (eq_refl (term312 _106676 _106693 s x' _51390)). Qed.
Lemma lem4448262 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (_51390 : _106693) : (term316 _106676 _106693 k s x' _51390) = (term319 _106676 _106693 k s x' _51390).
Proof. exact (MK_COMB (@lem4448260 _106693 k _51390) (@lem4448261 _106676 _106693 s x' _51390)). Qed.
Lemma lem4448263 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (_51390 : _106693) : (term311 _106676 _106693 s x' k _51390) = (term319 _106676 _106693 k s x' _51390).
Proof. exact (TRANS (@lem4448255 _106676 _106693 k s x' _51390) (@lem4448262 _106676 _106693 k s x' _51390)). Qed.
Lemma lem4448266 {_106676 _106693 : Type'} (_51390 : _106693) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term319 _106676 _106693 k s x' _51390.
Proof. exact (EQ_MP (@lem4448263 _106676 _106693 k s x' _51390) (@lem4448252 _106676 _106693 _51390 i k s x' h1)). Qed.
Lemma lem4448267 {_106676 _106693 : Type'} (_51390 : _106693) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term319 _106676 _106693 k s x' _51390.
Proof. exact (@lem4448266 _106676 _106693 _51390 i k s x' h1). Qed.
Lemma lem4448268 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term319 _106676 _106693 k s x' i.
Proof. exact (@lem4448267 _106676 _106693 i i k s x' h1). Qed.
Lemma lem4448271 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term312 _106676 _106693 s x' i.
Proof. exact (@lem4448268 _106676 _106693 i k s x' h1 (@lem4448223 _106676 _106693 i k s x' h1)). Qed.
Lemma lem4448272 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term320 _106676 _106693 s x' i.
Proof. exact (fun h0 : term321 _106676 _106693 s x' i => @lem4448271 _106676 _106693 i k s x' h1). Qed.
Lemma lem4448274 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4448275 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (i : _106693) : (term320 _106676 _106693 s x' i) = (term312 _106676 _106693 s x' i).
Proof. exact (@lem4448274 (term312 _106676 _106693 s x' i)). Qed.
Lemma lem4448276 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term312 _106676 _106693 s x' i.
Proof. exact (EQ_MP (@lem4448275 _106676 _106693 s x' i) (@lem4448272 _106676 _106693 i k s x' h1)). Qed.
Lemma lem4448279 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4448281 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (i : _106693) (_51391 : _106676) : (term18 _106676 _106693 s i _51391) = (term322 _106676 _106693 s i _51391).
Proof. exact (@lem4448279 (s i _51391)). Qed.
Lemma lem4448284 {_106676 _106693 : Type'} (_51391 : _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term322 _106676 _106693 s i _51391.
Proof. exact (EQ_MP (@lem4448281 _106676 _106693 s i _51391) (@lem4448138 _106676 _106693 _51391 i k s x' h1)). Qed.
Lemma lem4448285 {_106676 _106693 : Type'} (_51391 : _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term322 _106676 _106693 s i _51391.
Proof. exact (@lem4448284 _106676 _106693 _51391 i k s x' h1). Qed.
Lemma lem4448286 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term323 _106676 _106693 s x' i.
Proof. exact (@lem4448285 _106676 _106693 (x' i) i k s x' h1). Qed.
Lemma lem4448289 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : False.
Proof. exact (@lem4448286 _106676 _106693 i k s x' h1 (@lem4448276 _106676 _106693 i k s x' h1)). Qed.
Lemma lem4448290 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : term324.
Proof. exact (fun h0 : ~ False => @lem4448289 _106676 _106693 i k s x' h1). Qed.
Lemma lem4448292 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4448293 : term324 = False.
Proof. exact (@lem4448292 False). Qed.
Lemma lem4448294 {_106676 _106693 : Type'} (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term246 _106676 _106693 i k s x') : False.
Proof. exact (EQ_MP (@lem4448293) (@lem4448290 _106676 _106693 i k s x' h1)). Qed.
Lemma lem4448295 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term300 _106676 _106693 x i k s x') : False.
Proof. exact (or_elim (@lem4448048 _106676 _106693 x i k s x' h1) (fun h0 : term219 _106676 _106693 x k s i => @lem4448216 _106676 _106693 x k s i h0) (fun h0 : term246 _106676 _106693 i k s x' => @lem4448294 _106676 _106693 i k s x' h0)). Qed.
Lemma lem4448296 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term300 _106676 _106693 x i k s x') : (term300 _106676 _106693 x i k s x') = False.
Proof. exact (prop_ext (fun h2 : term300 _106676 _106693 x i k s x' => @lem4448295 _106676 _106693 x i k s x' h1) (fun h2 : False => @lem4448048 _106676 _106693 x i k s x' h1)). Qed.
Lemma lem4448297 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (x' : _106693 -> _106676) (h1 : term300 _106676 _106693 x i k s x') : False.
Proof. exact (EQ_MP (@lem4448296 _106676 _106693 x i k s x' h1) (@lem4448048 _106676 _106693 x i k s x' h1)). Qed.
Lemma lem4448298 {_106676 _106693 : Type'} (x : _106693 -> _106676) (i : _106693) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term303 _106676 _106693 x i k s) : False.
Proof. exact (ex_elim (@lem4447969 _106676 _106693 x i k s h1) (fun x' : _106693 -> _106676 => fun h0 : term302 _106676 _106693 x i k s x' => @lem4448297 _106676 _106693 x i k s x' h0)). Qed.
Lemma lem4448299 {_106676 _106693 : Type'} (x : _106693 -> _106676) (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term305 _106676 _106693 x k s) : False.
Proof. exact (ex_elim (@lem4447968 _106676 _106693 x k s h1) (fun i : _106693 => fun h0 : term304 _106676 _106693 x k s i => @lem4448298 _106676 _106693 x i k s h0)). Qed.
Lemma lem4448300 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term40 _106676 _106693 k s) : False.
Proof. exact (ex_elim (@lem4447967 _106676 _106693 k s h1) (fun x : _106693 -> _106676 => fun h0 : term306 _106676 _106693 k s x => @lem4448299 _106676 _106693 x k s h0)). Qed.
Lemma lem4448301 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term40 _106676 _106693 k s) : (term40 _106676 _106693 k s) = False.
Proof. exact (prop_ext (fun h2 : term40 _106676 _106693 k s => @lem4448300 _106676 _106693 k s h1) (fun h2 : False => @lem4447313 _106676 _106693 k s h1)). Qed.
Lemma lem4448302 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term40 _106676 _106693 k s) : False.
Proof. exact (EQ_MP (@lem4448301 _106676 _106693 k s h1) (@lem4447313 _106676 _106693 k s h1)). Qed.
Lemma lem4448303 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : term39 _106676 _106693 k s.
Proof. exact (fun h0 : term40 _106676 _106693 k s => @lem4448302 _106676 _106693 k s h0). Qed.
Lemma lem4448304 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term25 _106676 _106693 k s) = (term37 _106676 _106693 k s).
Proof. exact (EQ_MP (@lem4447312 _106676 _106693 k s) (@lem4448303 _106676 _106693 k s)). Qed.
Lemma lem4448309 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) : term49 _106676 _106693 s.
Proof. exact (fun k : _106693 -> Prop => @lem4448304 _106676 _106693 k s). Qed.
Lemma lem4448314 {_106676 _106693 : Type'} : term53 _106676 _106693.
Proof. exact (fun s : type1470 _106676 _106693 => @lem4448309 _106676 _106693 s). Qed.
Lemma lem4448315 {_106676 _106693 : Type'} : term52 _106676 _106693.
Proof. exact (EQ_MP (@lem4447308 _106676 _106693) (@lem4448314 _106676 _106693)). Qed.
Lemma lem4448316 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) : term325 _106676 _106693 s.
Proof. exact (@lem4448315 _106676 _106693 s). Qed.
Lemma lem4448317 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) : (term325 _106676 _106693 s) = (term48 _106676 _106693 s).
Proof. exact (eq_refl (term325 _106676 _106693 s)). Qed.
Lemma lem4448318 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) : term48 _106676 _106693 s.
Proof. exact (EQ_MP (@lem4448317 _106676 _106693 s) (@lem4448316 _106676 _106693 s)). Qed.
Lemma lem4448319 {_106676 _106693 : Type'} (s : type1470 _106676 _106693) (k : _106693 -> Prop) : term326 _106676 _106693 s k.
Proof. exact (@lem4448318 _106676 _106693 s k). Qed.
Lemma lem4448320 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term326 _106676 _106693 s k) = (term39 _106676 _106693 k s).
Proof. exact (eq_refl (term326 _106676 _106693 s k)). Qed.
Lemma lem4448321 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : term39 _106676 _106693 k s.
Proof. exact (EQ_MP (@lem4448320 _106676 _106693 k s) (@lem4448319 _106676 _106693 s k)). Qed.
Lemma lem4448323 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : term39 _106676 _106693 k s.
Proof. exact (@lem4447152 _106676 _106693 k s (@lem4448321 _106676 _106693 k s)). Qed.
Lemma lem4448324 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term40 _106676 _106693 k s) : False.
Proof. exact (@lem4448323 _106676 _106693 k s (@lem4447136 _106676 _106693 k s h1)). Qed.
Lemma lem4448325 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term40 _106676 _106693 k s) : (term40 _106676 _106693 k s) = False.
Proof. exact (prop_ext (fun h2 : term40 _106676 _106693 k s => @lem4448324 _106676 _106693 k s h1) (fun h2 : False => @lem4447136 _106676 _106693 k s h1)). Qed.
Lemma lem4448326 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) (h1 : term40 _106676 _106693 k s) : False.
Proof. exact (EQ_MP (@lem4448325 _106676 _106693 k s h1) (@lem4447136 _106676 _106693 k s h1)). Qed.
Lemma lem4448327 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : term39 _106676 _106693 k s.
Proof. exact (fun h0 : term40 _106676 _106693 k s => @lem4448326 _106676 _106693 k s h0). Qed.
Lemma lem4448328 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term25 _106676 _106693 k s) = (term37 _106676 _106693 k s).
Proof. exact (EQ_MP (@lem4447135 _106676 _106693 k s) (@lem4448327 _106676 _106693 k s)). Qed.
Lemma lem4448329 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term10 _106676 _106693 k s) = (term13 _106676 _106693 k s).
Proof. exact (EQ_MP (@lem4447131 _106676 _106693 k s) (@lem4448328 _106676 _106693 k s)). Qed.
Lemma lem4448331 {A : Type'} (P : A -> Prop) : term327 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem4448332 {A : Type'} (P : A -> Prop) : (term327 A P) = (term328 A P).
Proof. exact (eq_refl (term327 A P)). Qed.
Lemma lem4448333 {A : Type'} (P : A -> Prop) : term328 A P.
Proof. exact (EQ_MP (@lem4448332 A P) (@lem4448331 A P)). Qed.
Lemma lem4448334 {A : Type'} (P : A -> Prop) (Q : Prop) : term329 A P Q.
Proof. exact (@lem4448333 A P Q). Qed.
Lemma lem4448335 {A : Type'} (P : A -> Prop) (Q : Prop) : (term329 A P Q) = ((term330 A P Q) = (term331 A P Q)).
Proof. exact (eq_refl (term329 A P Q)). Qed.
Lemma lem4448337 {A B : Type'} (P : type1413 A B) : term332 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem4448338 {A B : Type'} (P : type1413 A B) : (term332 A B P) = ((term164 A B P) = (term165 A B P)).
Proof. exact (eq_refl (term332 A B P)). Qed.
Lemma lem4448340 {A K : Type'} (k : K -> Prop) : term333 A K k.
Proof. exact (@lem4408929 A K k). Qed.
Lemma lem4448341 {A K : Type'} (k : K -> Prop) : (term333 A K k) = (term334 A K k).
Proof. exact (eq_refl (term333 A K k)). Qed.
Lemma lem4448342 {A K : Type'} (k : K -> Prop) : term334 A K k.
Proof. exact (EQ_MP (@lem4448341 A K k) (@lem4448340 A K k)). Qed.
Lemma lem4448343 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term335 A K k s.
Proof. exact (@lem4448342 A K k s). Qed.
Lemma lem4448344 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term335 A K k s) = (((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term7 A K k s)).
Proof. exact (eq_refl (term335 A K k s)). Qed.
Lemma lem4448346 (t1 : Prop) : term336 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4448347 (t1 : Prop) : (term336 t1) = (term337 t1).
Proof. exact (eq_refl (term336 t1)). Qed.
Lemma lem4448348 (t1 : Prop) : term337 t1.
Proof. exact (EQ_MP (@lem4448347 t1) (@lem4448346 t1)). Qed.
Lemma lem4448349 (t1 : Prop) (t2 : Prop) : term338 t1 t2.
Proof. exact (@lem4448348 t1 t2). Qed.
Lemma lem4448350 (t1 : Prop) (t2 : Prop) : (term338 t1 t2) = (term339 t1 t2).
Proof. exact (eq_refl (term338 t1 t2)). Qed.
Lemma lem4448351 (t1 : Prop) (t2 : Prop) : term339 t1 t2.
Proof. exact (EQ_MP (@lem4448350 t1 t2) (@lem4448349 t1 t2)). Qed.
Lemma lem4448352 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term340 t1 t2 t3.
Proof. exact (@lem4448351 t1 t2 t3). Qed.
Lemma lem4448353 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term340 t1 t2 t3) = ((term341 t1 t2 t3) = (term342 t1 t2 t3)).
Proof. exact (eq_refl (term340 t1 t2 t3)). Qed.
Lemma lem4448354 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term341 t1 t2 t3) = (term342 t1 t2 t3).
Proof. exact (EQ_MP (@lem4448353 t1 t2 t3) (@lem4448352 t1 t2 t3)). Qed.
Lemma lem4448355 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term342 t1 t2 t3) = (term341 t1 t2 t3).
Proof. exact (SYM (@lem4448354 t1 t2 t3)). Qed.
Lemma lem4448380 {_83095 : Type'} : term343 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4448381 {_83095 : Type'} (p : _83095 -> Prop) : term344 _83095 p.
Proof. exact (@lem4448380 _83095 p). Qed.
Lemma lem4448382 {_83095 : Type'} (p : _83095 -> Prop) : (term344 _83095 p) = (term345 _83095 p).
Proof. exact (eq_refl (term344 _83095 p)). Qed.
Lemma lem4448383 {_83095 : Type'} (p : _83095 -> Prop) : term345 _83095 p.
Proof. exact (EQ_MP (@lem4448382 _83095 p) (@lem4448381 _83095 p)). Qed.
Lemma lem4448384 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term346 _83095 p x.
Proof. exact (@lem4448383 _83095 p x). Qed.
Lemma lem4448385 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term346 _83095 p x) = ((term347 _83095 x p) = (p x)).
Proof. exact (eq_refl (term346 _83095 p x)). Qed.
Lemma lem4448394 {A K : Type'} (k : K -> Prop) : term348 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4448395 {A K : Type'} (k : K -> Prop) : (term348 A K k) = (term349 A K k).
Proof. exact (eq_refl (term348 A K k)). Qed.
Lemma lem4448396 {A K : Type'} (k : K -> Prop) : term349 A K k.
Proof. exact (EQ_MP (@lem4448395 A K k) (@lem4448394 A K k)). Qed.
Lemma lem4448397 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term350 A K k s.
Proof. exact (@lem4448396 A K k s). Qed.
Lemma lem4448398 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term350 A K k s) = ((@cartesian_product A K k s) = (term351 A K k s)).
Proof. exact (eq_refl (term350 A K k s)). Qed.
Lemma lem4448400 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term352 A K k s.
Proof. exact (@lem9784 ((@cartesian_product A K k s) = (@EMPTY (K -> A)))). Qed.
Lemma lem4448401 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term352 A K k s) = (term353 A K k s).
Proof. exact (eq_refl (term352 A K k s)). Qed.
Lemma lem4448402 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term353 A K k s.
Proof. exact (EQ_MP (@lem4448401 A K k s) (@lem4448400 A K k s)). Qed.
Lemma lem4448404 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : term354 A K k s.
Proof. exact (h1). Qed.
Lemma lem4448405 {A : Type'} (x : A) : term355 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4448406 {A : Type'} (x : A) : (term355 A x) = (term356 A x).
Proof. exact (eq_refl (term355 A x)). Qed.
Lemma lem4448407 {A : Type'} (x : A) : term356 A x.
Proof. exact (EQ_MP (@lem4448406 A x) (@lem4448405 A x)). Qed.
Lemma lem4448408 {A : Type'} (x : A) : term357 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4448425 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (@cartesian_product A K k s) = (@EMPTY (K -> A)).
Proof. exact (h1). Qed.
Lemma lem4448426 {A K : Type'} (z : K -> A) : (@IN (K -> A) z) = (@IN (K -> A) z).
Proof. exact (eq_refl (@IN (K -> A) z)). Qed.
Lemma lem4448427 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term358 A K z k s) = (@IN (K -> A) z (@EMPTY (K -> A))).
Proof. exact (MK_COMB (@lem4448426 A K z) (@lem4448425 A K k s h1)). Qed.
Lemma lem4448429 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4448408 A x (@lem4448407 A x)). Qed.
Lemma lem4448430 {A K : Type'} (x : K -> A) : (@IN (K -> A) x (@EMPTY (K -> A))) = False.
Proof. exact (@lem4448429 (K -> A) x). Qed.
Lemma lem4448431 {A K : Type'} (z : K -> A) : (@IN (K -> A) z (@EMPTY (K -> A))) = False.
Proof. exact (@lem4448430 A K z). Qed.
Lemma lem4448432 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term358 A K z k s) = False.
Proof. exact (TRANS (@lem4448427 A K z k s h1) (@lem4448431 A K z)). Qed.
Lemma lem4448433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4448434 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term359 A K z k s) = (and False).
Proof. exact (MK_COMB (@lem4448433) (@lem4448432 A K z k s h1)). Qed.
Lemma lem4448435 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@IN K i k).
Proof. exact (eq_refl (@IN K i k)). Qed.
Lemma lem4448436 {A K : Type'} (z : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term360 A K z s i k) = (term361 K i k).
Proof. exact (MK_COMB (@lem4448434 A K z k s h1) (@lem4448435 K i k)). Qed.
Lemma lem4448438 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4448439 {K : Type'} (i : K) (k : K -> Prop) : (term361 K i k) = False.
Proof. exact (@lem4448438 (@IN K i k)). Qed.
Lemma lem4448440 {A K : Type'} (z : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term360 A K z s i k) = False.
Proof. exact (TRANS (@lem4448436 A K z i k s h1) (@lem4448439 K i k)). Qed.
Lemma lem4448441 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4448442 {A K : Type'} (z : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term362 A K z s i k) = (imp False).
Proof. exact (MK_COMB (@lem4448441) (@lem4448440 A K z i k s h1)). Qed.
Lemma lem4448443 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) : (term312 A K P z i) = (term312 A K P z i).
Proof. exact (eq_refl (term312 A K P z i)). Qed.
Lemma lem4448444 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term363 A K s k P z i) = (term364 A K P z i).
Proof. exact (MK_COMB (@lem4448442 A K z i k s h1) (@lem4448443 A K P z i)). Qed.
Lemma lem4448446 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4448447 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) : (term364 A K P z i) = True.
Proof. exact (@lem4448446 (term312 A K P z i)). Qed.
Lemma lem4448448 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term363 A K s k P z i) = True.
Proof. exact (TRANS (@lem4448444 A K P z i k s h1) (@lem4448447 A K P z i)). Qed.
Lemma lem4448449 {A K : Type'} (P : type1470 A K) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term365 A K s k P z) = (term366 K).
Proof. exact (fun_ext (fun i : K => @lem4448448 A K P z i k s h1)). Qed.
Lemma lem4448450 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4448451 {A K : Type'} (P : type1470 A K) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term367 A K s k P z) = (term368 K).
Proof. exact (MK_COMB (@lem4448450 K) (@lem4448449 A K P z k s h1)). Qed.
Lemma lem4448453 {A : Type'} (t : Prop) : (term129 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4448454 {K : Type'} (t : Prop) : (term129 K t) = t.
Proof. exact (@lem4448453 K t). Qed.
Lemma lem4448455 {K : Type'} : (term368 K) = True.
Proof. exact (@lem4448454 K True). Qed.
Lemma lem4448456 {A K : Type'} (P : type1470 A K) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term367 A K s k P z) = True.
Proof. exact (TRANS (@lem4448451 A K P z k s h1) (@lem4448455 K)). Qed.
Lemma lem4448457 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term369 A K s k P) = (term370 A K).
Proof. exact (fun_ext (fun z : K -> A => @lem4448456 A K P z k s h1)). Qed.
Lemma lem4448458 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4448459 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term371 A K s k P) = (term372 A K).
Proof. exact (MK_COMB (@lem4448458 A K) (@lem4448457 A K P k s h1)). Qed.
Lemma lem4448461 {A : Type'} (t : Prop) : (term129 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4448462 {A K : Type'} (t : Prop) : (term373 A K t) = t.
Proof. exact (@lem4448461 (K -> A) t). Qed.
Lemma lem4448463 {A K : Type'} : (term372 A K) = True.
Proof. exact (@lem4448462 A K True). Qed.
Lemma lem4448464 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term371 A K s k P) = True.
Proof. exact (TRANS (@lem4448459 A K P k s h1) (@lem4448463 A K)). Qed.
Lemma lem4448465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4448466 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term374 A K s k P) = (@eq Prop True).
Proof. exact (MK_COMB (@lem4448465) (@lem4448464 A K P k s h1)). Qed.
Lemma lem4448472 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (@cartesian_product A K k s) = (@EMPTY (K -> A)).
Proof. exact (h1). Qed.
Lemma lem4448473 {A K : Type'} : (@eq ((K -> A) -> Prop)) = (@eq ((K -> A) -> Prop)).
Proof. exact (eq_refl (@eq ((K -> A) -> Prop))). Qed.
Lemma lem4448474 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term375 A K k s) = (@eq ((K -> A) -> Prop) (@EMPTY (K -> A))).
Proof. exact (MK_COMB (@lem4448473 A K) (@lem4448472 A K k s h1)). Qed.
Lemma lem4448475 {A K : Type'} : (@EMPTY (K -> A)) = (@EMPTY (K -> A)).
Proof. exact (eq_refl (@EMPTY (K -> A))). Qed.
Lemma lem4448476 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = ((@EMPTY (K -> A)) = (@EMPTY (K -> A))).
Proof. exact (MK_COMB (@lem4448474 A K k s h1) (@lem4448475 A K)). Qed.
Lemma lem4448478 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4448479 {A K : Type'} (x : type805 A K) : (x = x) = True.
Proof. exact (@lem4448478 (type805 A K) x). Qed.
Lemma lem4448480 {A K : Type'} : ((@EMPTY (K -> A)) = (@EMPTY (K -> A))) = True.
Proof. exact (@lem4448479 A K (@EMPTY (K -> A))). Qed.
Lemma lem4448481 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = True.
Proof. exact (TRANS (@lem4448476 A K k s h1) (@lem4448480 A K)). Qed.
Lemma lem4448482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4448483 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term376 A K k s) = (or True).
Proof. exact (MK_COMB (@lem4448482) (@lem4448481 A K k s h1)). Qed.
Lemma lem4448496 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term377 A K k s P) = (term377 A K k s P).
Proof. exact (eq_refl (term377 A K k s P)). Qed.
Lemma lem4448497 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term378 A K k s P) = (term379 A K k s P).
Proof. exact (MK_COMB (@lem4448483 A K k s h1) (@lem4448496 A K k s P)). Qed.
Lemma lem4448499 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4448500 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term379 A K k s P) = True.
Proof. exact (@lem4448499 (term377 A K k s P)). Qed.
Lemma lem4448501 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term378 A K k s P) = True.
Proof. exact (TRANS (@lem4448497 A K P k s h1) (@lem4448500 A K k s P)). Qed.
Lemma lem4448502 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((term371 A K s k P) = (term378 A K k s P)) = (True = True).
Proof. exact (MK_COMB (@lem4448466 A K P k s h1) (@lem4448501 A K P k s h1)). Qed.
Lemma lem4448504 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4448505 : (True = True) = True.
Proof. exact (@lem4448504 True). Qed.
Lemma lem4448506 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((term371 A K s k P) = (term378 A K k s P)) = True.
Proof. exact (TRANS (@lem4448502 A K P k s h1) (@lem4448505)). Qed.
Lemma lem4448507 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : True = ((term371 A K s k P) = (term378 A K k s P)).
Proof. exact (SYM (@lem4448506 A K P k s h1)). Qed.
Lemma lem4448508 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term371 A K s k P) = (term378 A K k s P).
Proof. exact (EQ_MP (@lem4448507 A K P k s h1) (@lem0)). Qed.
Lemma lem4448514 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term380 A K k s.
Proof. exact (@lem82 ((@cartesian_product A K k s) = (@EMPTY (K -> A)))). Qed.
Lemma lem4448544 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = False.
Proof. exact (@lem4448514 A K k s (@lem4448404 A K k s h1)). Qed.
Lemma lem4448545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4448546 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : (term376 A K k s) = (or False).
Proof. exact (MK_COMB (@lem4448545) (@lem4448544 A K k s h1)). Qed.
Lemma lem4448559 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term377 A K k s P) = (term377 A K k s P).
Proof. exact (eq_refl (term377 A K k s P)). Qed.
Lemma lem4448560 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : (term378 A K k s P) = (term381 A K k s P).
Proof. exact (MK_COMB (@lem4448546 A K k s h1) (@lem4448559 A K k s P)). Qed.
Lemma lem4448562 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4448563 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term381 A K k s P) = (term377 A K k s P).
Proof. exact (@lem4448562 (term377 A K k s P)). Qed.
Lemma lem4448576 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : (term378 A K k s P) = (term377 A K k s P).
Proof. exact (TRANS (@lem4448560 A K P k s h1) (@lem4448563 A K k s P)). Qed.
Lemma lem4448577 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term374 A K s k P) = (term374 A K s k P).
Proof. exact (eq_refl (term374 A K s k P)). Qed.
Lemma lem4448578 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : ((term371 A K s k P) = (term378 A K k s P)) = ((term371 A K s k P) = (term377 A K k s P)).
Proof. exact (MK_COMB (@lem4448577 A K s k P) (@lem4448576 A K P k s h1)). Qed.
Lemma lem4448581 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : ((term371 A K s k P) = (term377 A K k s P)) = ((term371 A K s k P) = (term378 A K k s P)).
Proof. exact (SYM (@lem4448578 A K P k s h1)). Qed.
Lemma lem4448597 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term351 A K k s).
Proof. exact (EQ_MP (@lem4448398 A K k s) (@lem4448397 A K k s)). Qed.
Lemma lem4448598 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term351 A K k s).
Proof. exact (@lem4448597 A K k s). Qed.
Lemma lem4448611 {A K : Type'} (z : K -> A) : (@IN (K -> A) z) = (@IN (K -> A) z).
Proof. exact (eq_refl (@IN (K -> A) z)). Qed.
Lemma lem4448612 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term358 A K z k s) = (term382 A K z k s).
Proof. exact (MK_COMB (@lem4448611 A K z) (@lem4448598 A K k s)). Qed.
Lemma lem4448614 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term347 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4448385 _83095 p x) (@lem4448384 _83095 p x)). Qed.
Lemma lem4448615 {A K : Type'} (p : type805 A K) (x : K -> A) : (term383 A K x p) = (p x).
Proof. exact (@lem4448614 (K -> A) p x). Qed.
Lemma lem4448616 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (z : K -> A) : (term384 A K z k s) = (term385 A K k s z).
Proof. exact (@lem4448615 A K (term386 A K k s) z). Qed.
Lemma lem4448617 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term385 A K k s f) = (term387 A K k f s).
Proof. exact (eq_refl (term385 A K k s f)). Qed.
Lemma lem4448618 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4448619 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term388 A K GEN_PVAR_140 k s f) = (term389 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4448618 A K GEN_PVAR_140) (@lem4448617 A K k f s)). Qed.
Lemma lem4448620 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4448621 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term390 A K GEN_PVAR_140 k s f) = (term391 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4448619 A K GEN_PVAR_140 k f s) (@lem4448620 A K f)). Qed.
Lemma lem4448622 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term392 A K GEN_PVAR_140 k s) = (term393 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4448621 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4448623 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4448624 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term394 A K GEN_PVAR_140 k s) = (term395 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4448623 A K) (@lem4448622 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4448625 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term396 A K k s) = (term397 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4448624 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4448626 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4448627 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term398 A K k s) = (term351 A K k s).
Proof. exact (MK_COMB (@lem4448626 A K) (@lem4448625 A K k s)). Qed.
Lemma lem4448628 {A K : Type'} (z : K -> A) : (@IN (K -> A) z) = (@IN (K -> A) z).
Proof. exact (eq_refl (@IN (K -> A) z)). Qed.
Lemma lem4448629 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term384 A K z k s) = (term382 A K z k s).
Proof. exact (MK_COMB (@lem4448628 A K z) (@lem4448627 A K k s)). Qed.
Lemma lem4448630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4448631 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term399 A K z k s) = (term400 A K z k s).
Proof. exact (MK_COMB (@lem4448630) (@lem4448629 A K z k s)). Qed.
Lemma lem4448632 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term385 A K k s z) = (term387 A K k z s).
Proof. exact (eq_refl (term385 A K k s z)). Qed.
Lemma lem4448633 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : ((term384 A K z k s) = (term385 A K k s z)) = ((term382 A K z k s) = (term387 A K k z s)).
Proof. exact (MK_COMB (@lem4448631 A K z k s) (@lem4448632 A K k z s)). Qed.
Lemma lem4448634 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term382 A K z k s) = (term387 A K k z s).
Proof. exact (EQ_MP (@lem4448633 A K k z s) (@lem4448616 A K k s z)). Qed.
Lemma lem4448643 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term358 A K z k s) = (term387 A K k z s).
Proof. exact (TRANS (@lem4448612 A K z k s) (@lem4448634 A K k z s)). Qed.
Lemma lem4448644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4448645 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term359 A K z k s) = (term401 A K k z s).
Proof. exact (MK_COMB (@lem4448644) (@lem4448643 A K k z s)). Qed.
Lemma lem4448646 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@IN K i k).
Proof. exact (eq_refl (@IN K i k)). Qed.
Lemma lem4448647 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) : (term360 A K z s i k) = (term402 A K z s i k).
Proof. exact (MK_COMB (@lem4448645 A K k z s) (@lem4448646 K i k)). Qed.
Lemma lem4448650 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4448651 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) : (term362 A K z s i k) = (term403 A K z s i k).
Proof. exact (MK_COMB (@lem4448650) (@lem4448647 A K z s i k)). Qed.
Lemma lem4448652 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) : (term312 A K P z i) = (term312 A K P z i).
Proof. exact (eq_refl (term312 A K P z i)). Qed.
Lemma lem4448653 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (z : K -> A) (i : K) : (term363 A K s k P z i) = (term404 A K s k P z i).
Proof. exact (MK_COMB (@lem4448651 A K z s i k) (@lem4448652 A K P z i)). Qed.
Lemma lem4448656 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (z : K -> A) : (term365 A K s k P z) = (term405 A K s k P z).
Proof. exact (fun_ext (fun i : K => @lem4448653 A K s k P z i)). Qed.
Lemma lem4448657 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4448658 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (z : K -> A) : (term367 A K s k P z) = (term406 A K s k P z).
Proof. exact (MK_COMB (@lem4448657 K) (@lem4448656 A K s k P z)). Qed.
Lemma lem4448663 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term369 A K s k P) = (term407 A K s k P).
Proof. exact (fun_ext (fun z : K -> A => @lem4448658 A K s k P z)). Qed.
Lemma lem4448664 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4448665 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term371 A K s k P) = (term408 A K s k P).
Proof. exact (MK_COMB (@lem4448664 A K) (@lem4448663 A K s k P)). Qed.
Lemma lem4448670 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4448671 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term374 A K s k P) = (term409 A K s k P).
Proof. exact (MK_COMB (@lem4448670) (@lem4448665 A K s k P)). Qed.
Lemma lem4448684 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term377 A K k s P) = (term377 A K k s P).
Proof. exact (eq_refl (term377 A K k s P)). Qed.
Lemma lem4448685 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term371 A K s k P) = (term377 A K k s P)) = ((term408 A K s k P) = (term377 A K k s P)).
Proof. exact (MK_COMB (@lem4448671 A K s k P) (@lem4448684 A K k s P)). Qed.
Lemma lem4448688 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term408 A K s k P) = (term377 A K k s P)) = ((term371 A K s k P) = (term377 A K k s P)).
Proof. exact (SYM (@lem4448685 A K k s P)). Qed.
Lemma lem4448689 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term408 A K s k P) : term408 A K s k P.
Proof. exact (h1). Qed.
Lemma lem4448691 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4448692 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term410 A K s k P) = (term411 A K s k P).
Proof. exact (@lem4448691 (term410 A K s k P)). Qed.
Lemma lem4448693 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term411 A K s k P) = (term410 A K s k P).
Proof. exact (SYM (@lem4448692 A K s k P)). Qed.
Lemma lem4448694 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term412 A K s k P) : term412 A K s k P.
Proof. exact (h1). Qed.
Lemma lem4448697 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term411 A K s k P) : term411 A K s k P.
Proof. exact (h1). Qed.
Lemma lem4448698 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : term413 A K s k P.
Proof. exact (fun h0 : term411 A K s k P => @lem4448697 A K s k P h0). Qed.
Lemma lem4448699 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term413 A K s k P) : term413 A K s k P.
Proof. exact (h1). Qed.
Lemma lem4448700 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term411 A K s k P) : term411 A K s k P.
Proof. exact (h1). Qed.
Lemma lem4448701 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term411 A K s k P) (h2 : term413 A K s k P) : term411 A K s k P.
Proof. exact (@lem4448699 A K s k P h2 (@lem4448700 A K s k P h1)). Qed.
Lemma lem4448702 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term411 A K s k P) : term414 A K s k P.
Proof. exact (fun h0 : term413 A K s k P => @lem4448701 A K s k P h1 h0). Qed.
Lemma lem4448703 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term413 A K s k P) : term413 A K s k P.
Proof. exact (h1). Qed.
Lemma lem4448704 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term411 A K s k P) (h2 : term413 A K s k P) : term411 A K s k P.
Proof. exact (@lem4448702 A K s k P h1 (@lem4448703 A K s k P h2)). Qed.
Lemma lem4448705 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term413 A K s k P) : term413 A K s k P.
Proof. exact (fun h0 : term411 A K s k P => @lem4448704 A K s k P h0 h1). Qed.
Lemma lem4448706 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : term415 A K s k P.
Proof. exact (fun h0 : term413 A K s k P => @lem4448705 A K s k P h0). Qed.
Lemma lem4448709 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : term413 A K s k P.
Proof. exact (@lem4448706 A K s k P (@lem4448698 A K s k P)). Qed.
Lemma lem4448710 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : term413 A K s k P.
Proof. exact (@lem4448709 A K s k P). Qed.
Lemma lem4448724 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4448725 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term411 A K s k P) = (term416 A K s k P).
Proof. exact (@lem4448724 (term412 A K s k P)). Qed.
Lemma lem4448727 (t : Prop) : (term45 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4448728 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term416 A K s k P) = (term410 A K s k P).
Proof. exact (@lem4448727 (term410 A K s k P)). Qed.
Lemma lem4448731 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term411 A K s k P) = (term410 A K s k P).
Proof. exact (TRANS (@lem4448725 A K s k P) (@lem4448728 A K s k P)). Qed.
Lemma lem4448764 {A K : Type'} (k : K -> Prop) (P : type1470 A K) : (term417 A K k P) = (term418 A K k P).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4448731 A K s k P)). Qed.
Lemma lem4448765 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4448766 {A K : Type'} (k : K -> Prop) (P : type1470 A K) : (term419 A K k P) = (term420 A K k P).
Proof. exact (MK_COMB (@lem4448765 A K) (@lem4448764 A K k P)). Qed.
Lemma lem4448771 {A K : Type'} (P : type1470 A K) : (term421 A K P) = (term422 A K P).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4448766 A K k P)). Qed.
Lemma lem4448772 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4448773 {A K : Type'} (P : type1470 A K) : (term423 A K P) = (term424 A K P).
Proof. exact (MK_COMB (@lem4448772 K) (@lem4448771 A K P)). Qed.
Lemma lem4448778 {A K : Type'} : (term425 A K) = (term426 A K).
Proof. exact (fun_ext (fun P : type1470 A K => @lem4448773 A K P)). Qed.
Lemma lem4448779 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4448788 {A K : Type'} : (term427 A K) = (term428 A K).
Proof. exact (MK_COMB (@lem4448779 A K) (@lem4448778 A K)). Qed.
Lemma lem4448789 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) : (term312 A K P z i) = (term312 A K P z i).
Proof. exact (eq_refl (term312 A K P z i)). Qed.
Lemma lem4448790 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@IN K i k).
Proof. exact (eq_refl (@IN K i k)). Qed.
Lemma lem4448795 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term429 A K k z s i) = (term429 A K k z s i).
Proof. exact (eq_refl (term429 A K k z s i)). Qed.
Lemma lem4448796 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term430 A K k z s) = (term430 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4448795 A K k z s i)). Qed.
Lemma lem4448797 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4448798 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term431 A K k z s) = (term431 A K k z s).
Proof. exact (MK_COMB (@lem4448797 K) (@lem4448796 A K k z s)). Qed.
Lemma lem4448801 {A K : Type'} (k : K -> Prop) (z : K -> A) : (term432 A K k z) = (term432 A K k z).
Proof. exact (eq_refl (term432 A K k z)). Qed.
Lemma lem4448802 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term387 A K k z s) = (term387 A K k z s).
Proof. exact (MK_COMB (@lem4448801 A K k z) (@lem4448798 A K k z s)). Qed.
Lemma lem4448803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4448804 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term401 A K k z s) = (term401 A K k z s).
Proof. exact (MK_COMB (@lem4448803) (@lem4448802 A K k z s)). Qed.
Lemma lem4448805 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) : (term402 A K z s i k) = (term402 A K z s i k).
Proof. exact (MK_COMB (@lem4448804 A K k z s) (@lem4448790 K i k)). Qed.
Lemma lem4448806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4448807 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) : (term403 A K z s i k) = (term403 A K z s i k).
Proof. exact (MK_COMB (@lem4448806) (@lem4448805 A K z s i k)). Qed.
Lemma lem4448808 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (z : K -> A) (i : K) : (term404 A K s k P z i) = (term404 A K s k P z i).
Proof. exact (MK_COMB (@lem4448807 A K z s i k) (@lem4448789 A K P z i)). Qed.
Lemma lem4448809 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (z : K -> A) : (term405 A K s k P z) = (term405 A K s k P z).
Proof. exact (fun_ext (fun i : K => @lem4448808 A K s k P z i)). Qed.
Lemma lem4448810 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4448811 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (z : K -> A) : (term406 A K s k P z) = (term406 A K s k P z).
Proof. exact (MK_COMB (@lem4448810 K) (@lem4448809 A K s k P z)). Qed.
Lemma lem4448812 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term407 A K s k P) = (term407 A K s k P).
Proof. exact (fun_ext (fun z : K -> A => @lem4448811 A K s k P z)). Qed.
Lemma lem4448813 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4448814 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term408 A K s k P) = (term408 A K s k P).
Proof. exact (MK_COMB (@lem4448813 A K) (@lem4448812 A K s k P)). Qed.
Lemma lem4448823 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term433 A K k s P i x) = (term433 A K k s P i x).
Proof. exact (eq_refl (term433 A K k s P i x)). Qed.
Lemma lem4448824 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term434 A K k s P i) = (term434 A K k s P i).
Proof. exact (fun_ext (fun x : A => @lem4448823 A K k s P i x)). Qed.
Lemma lem4448825 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4448826 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term435 A K k s P i) = (term435 A K k s P i).
Proof. exact (MK_COMB (@lem4448825 A) (@lem4448824 A K k s P i)). Qed.
Lemma lem4448827 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term436 A K k s P) = (term436 A K k s P).
Proof. exact (fun_ext (fun i : K => @lem4448826 A K k s P i)). Qed.
Lemma lem4448828 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4448829 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term377 A K k s P) = (term377 A K k s P).
Proof. exact (MK_COMB (@lem4448828 K) (@lem4448827 A K k s P)). Qed.
Lemma lem4448830 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4448831 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term437 A K k s P) = (term437 A K k s P).
Proof. exact (MK_COMB (@lem4448830) (@lem4448829 A K k s P)). Qed.
Lemma lem4448832 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term410 A K s k P) = (term410 A K s k P).
Proof. exact (MK_COMB (@lem4448831 A K k s P) (@lem4448814 A K s k P)). Qed.
Lemma lem4448833 {A K : Type'} (k : K -> Prop) (P : type1470 A K) : (term418 A K k P) = (term418 A K k P).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4448832 A K s k P)). Qed.
Lemma lem4448834 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4448835 {A K : Type'} (k : K -> Prop) (P : type1470 A K) : (term420 A K k P) = (term420 A K k P).
Proof. exact (MK_COMB (@lem4448834 A K) (@lem4448833 A K k P)). Qed.
Lemma lem4448836 {A K : Type'} (P : type1470 A K) : (term422 A K P) = (term422 A K P).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4448835 A K k P)). Qed.
Lemma lem4448837 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4448838 {A K : Type'} (P : type1470 A K) : (term424 A K P) = (term424 A K P).
Proof. exact (MK_COMB (@lem4448837 K) (@lem4448836 A K P)). Qed.
Lemma lem4448839 {A K : Type'} : (term426 A K) = (term426 A K).
Proof. exact (fun_ext (fun P : type1470 A K => @lem4448838 A K P)). Qed.
Lemma lem4448840 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4448841 {A K : Type'} : (term428 A K) = (term428 A K).
Proof. exact (MK_COMB (@lem4448840 A K) (@lem4448839 A K)). Qed.
Lemma lem4448906 {A K : Type'} : (term427 A K) = (term428 A K).
Proof. exact (TRANS (@lem4448788 A K) (@lem4448841 A K)). Qed.
Lemma lem4448907 {A K : Type'} : (term428 A K) = (term427 A K).
Proof. exact (SYM (@lem4448906 A K)). Qed.
Lemma lem4448908 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term377 A K k s P.
Proof. exact (h1). Qed.
Lemma lem4448909 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term402 A K z s i k.
Proof. exact (h1). Qed.
Lemma lem4448911 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4448912 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) : (term312 A K P z i) = (term438 A K P z i).
Proof. exact (@lem4448911 (term312 A K P z i)). Qed.
Lemma lem4448913 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) : (term438 A K P z i) = (term312 A K P z i).
Proof. exact (SYM (@lem4448912 A K P z i)). Qed.
Lemma lem4448914 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) (h1 : term321 A K P z i) : term321 A K P z i.
Proof. exact (h1). Qed.
Lemma lem4448921 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term439 A K k x s i) = (term440 A K k x s i).
Proof. exact (@lem17045 (@IN K i k) (term15 A K x s i)). Qed.
Lemma lem4448922 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (P i x) = (P i x).
Proof. exact (eq_refl (P i x)). Qed.
Lemma lem4448923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4448924 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term441 A K k x s i) = (term442 A K k x s i).
Proof. exact (MK_COMB (@lem4448923) (@lem4448921 A K k x s i)). Qed.
Lemma lem4448925 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term443 A K k s P i x) = (term444 A K k s P i x).
Proof. exact (MK_COMB (@lem4448924 A K k x s i) (@lem4448922 A K P i x)). Qed.
Lemma lem4448926 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term433 A K k s P i x) = (term443 A K k s P i x).
Proof. exact (@lem17265 (term445 A K k x s i) (P i x)). Qed.
Lemma lem4448927 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term433 A K k s P i x) = (term444 A K k s P i x).
Proof. exact (TRANS (@lem4448926 A K k s P i x) (@lem4448925 A K k s P i x)). Qed.
Lemma lem4448928 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term434 A K k s P i) = (term446 A K k s P i).
Proof. exact (fun_ext (fun x : A => @lem4448927 A K k s P i x)). Qed.
Lemma lem4448929 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4448930 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term435 A K k s P i) = (term447 A K k s P i).
Proof. exact (MK_COMB (@lem4448929 A) (@lem4448928 A K k s P i)). Qed.
Lemma lem4448931 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term436 A K k s P) = (term448 A K k s P).
Proof. exact (fun_ext (fun i : K => @lem4448930 A K k s P i)). Qed.
Lemma lem4448932 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4448989 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term377 A K k s P) = (term449 A K k s P).
Proof. exact (MK_COMB (@lem4448932 K) (@lem4448931 A K k s P)). Qed.
Lemma lem4448990 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term449 A K k s P.
Proof. exact (EQ_MP (@lem4448989 A K k s P) (@lem4448908 A K k s P h1)). Qed.
Lemma lem4448998 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term429 A K k z s i) = (term450 A K k z s i).
Proof. exact (@lem17265 (@IN K i k) (term451 A K z s i)). Qed.
Lemma lem4448999 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term430 A K k z s) = (term452 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4448998 A K k z s i)). Qed.
Lemma lem4449000 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4449001 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term431 A K k z s) = (term453 A K k z s).
Proof. exact (MK_COMB (@lem4449000 K) (@lem4448999 A K k z s)). Qed.
Lemma lem4449003 {A K : Type'} (k : K -> Prop) (z : K -> A) : (term432 A K k z) = (term432 A K k z).
Proof. exact (eq_refl (term432 A K k z)). Qed.
Lemma lem4449004 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term387 A K k z s) = (term454 A K k z s).
Proof. exact (MK_COMB (@lem4449003 A K k z) (@lem4449001 A K k z s)). Qed.
Lemma lem4449005 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@IN K i k).
Proof. exact (eq_refl (@IN K i k)). Qed.
Lemma lem4449006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4449007 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term401 A K k z s) = (term455 A K k z s).
Proof. exact (MK_COMB (@lem4449006) (@lem4449004 A K k z s)). Qed.
Lemma lem4449060 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) : (term402 A K z s i k) = (term456 A K z s i k).
Proof. exact (MK_COMB (@lem4449007 A K k z s) (@lem4449005 K i k)). Qed.
Lemma lem4449061 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term456 A K z s i k.
Proof. exact (EQ_MP (@lem4449060 A K z s i k) (@lem4448909 A K z s i k h1)). Qed.
Lemma lem4449067 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) (h1 : term321 A K P z i) : term321 A K P z i.
Proof. exact (h1). Qed.
Lemma lem4449094 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term444 A K k s P i x) = (term444 A K k s P i x).
Proof. exact (eq_refl (term444 A K k s P i x)). Qed.
Lemma lem4449095 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term446 A K k s P i) = (term446 A K k s P i).
Proof. exact (fun_ext (fun x : A => @lem4449094 A K k s P i x)). Qed.
Lemma lem4449096 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4449097 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term447 A K k s P i) = (term447 A K k s P i).
Proof. exact (MK_COMB (@lem4449096 A) (@lem4449095 A K k s P i)). Qed.
Lemma lem4449098 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term448 A K k s P) = (term448 A K k s P).
Proof. exact (fun_ext (fun i : K => @lem4449097 A K k s P i)). Qed.
Lemma lem4449099 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4449100 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term449 A K k s P) = (term449 A K k s P).
Proof. exact (MK_COMB (@lem4449099 K) (@lem4449098 A K k s P)). Qed.
Lemma lem4449101 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term449 A K k s P.
Proof. exact (EQ_MP (@lem4449100 A K k s P) (@lem4448990 A K k s P h1)). Qed.
Lemma lem4449106 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@IN K i k).
Proof. exact (eq_refl (@IN K i k)). Qed.
Lemma lem4449107 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4449112 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4449113 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4449112 K A f x). Qed.
Lemma lem4449115 {A K : Type'} (z : K -> A) (i : K) : (z i) = (@I (K -> A) z i).
Proof. exact (@lem4449113 A K z i). Qed.
Lemma lem4449118 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4449119 {A K : Type'} (z : K -> A) (i : K) : (term457 A K z i) = (term458 A K z i).
Proof. exact (MK_COMB (@lem4449107 A) (@lem4449115 A K z i)). Qed.
Lemma lem4449120 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) : (term451 A K z s i) = (term459 A K z s i).
Proof. exact (MK_COMB (@lem4449119 A K z i) (@lem4449118 A K s i)). Qed.
Lemma lem4449129 {K : Type'} (i : K) (k : K -> Prop) : (term460 K i k) = (term460 K i k).
Proof. exact (eq_refl (term460 K i k)). Qed.
Lemma lem4449130 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term450 A K k z s i) = (term461 A K k z s i).
Proof. exact (MK_COMB (@lem4449129 K i k) (@lem4449120 A K z s i)). Qed.
Lemma lem4449131 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term452 A K k z s) = (term462 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4449130 A K k z s i)). Qed.
Lemma lem4449132 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4449133 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term453 A K k z s) = (term463 A K k z s).
Proof. exact (MK_COMB (@lem4449132 K) (@lem4449131 A K k z s)). Qed.
Lemma lem4449140 {A K : Type'} (k : K -> Prop) (z : K -> A) : (term432 A K k z) = (term432 A K k z).
Proof. exact (eq_refl (term432 A K k z)). Qed.
Lemma lem4449141 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term454 A K k z s) = (term464 A K k z s).
Proof. exact (MK_COMB (@lem4449140 A K k z) (@lem4449133 A K k z s)). Qed.
Lemma lem4449142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4449143 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term455 A K k z s) = (term465 A K k z s).
Proof. exact (MK_COMB (@lem4449142) (@lem4449141 A K k z s)). Qed.
Lemma lem4449144 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) : (term456 A K z s i k) = (term466 A K z s i k).
Proof. exact (MK_COMB (@lem4449143 A K k z s) (@lem4449106 K i k)). Qed.
Lemma lem4449145 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term466 A K z s i k.
Proof. exact (EQ_MP (@lem4449144 A K z s i k) (@lem4449061 A K z s i k h1)). Qed.
Lemma lem4449146 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4449153 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4449154 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4449153 K A f x). Qed.
Lemma lem4449156 {A K : Type'} (z : K -> A) (i : K) : (z i) = (@I (K -> A) z i).
Proof. exact (@lem4449154 A K z i). Qed.
Lemma lem4449157 {A K : Type'} (P : type1470 A K) (i : K) : (P i) = (P i).
Proof. exact (eq_refl (P i)). Qed.
Lemma lem4449158 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) : (term312 A K P z i) = (term467 A K P z i).
Proof. exact (MK_COMB (@lem4449157 A K P i) (@lem4449156 A K z i)). Qed.
Lemma lem4449159 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) : (term321 A K P z i) = (term468 A K P z i).
Proof. exact (MK_COMB (@lem4449146) (@lem4449158 A K P z i)). Qed.
Lemma lem4449162 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term464 A K k z s.
Proof. exact (proj1 (@lem4449145 A K z s i k h1)). Qed.
Lemma lem4449163 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term463 A K k z s.
Proof. exact (proj2 (@lem4449162 A K z s i k h1)). Qed.
Lemma lem4449178 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term444 A K k s P i x) = (term444 A K k s P i x).
Proof. exact (eq_refl (term444 A K k s P i x)). Qed.
Lemma lem4449179 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term446 A K k s P i) = (term446 A K k s P i).
Proof. exact (fun_ext (fun x : A => @lem4449178 A K k s P i x)). Qed.
Lemma lem4449180 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4449181 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (i : K) : (term447 A K k s P i) = (term447 A K k s P i).
Proof. exact (MK_COMB (@lem4449180 A) (@lem4449179 A K k s P i)). Qed.
Lemma lem4449182 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term448 A K k s P) = (term448 A K k s P).
Proof. exact (fun_ext (fun i : K => @lem4449181 A K k s P i)). Qed.
Lemma lem4449183 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4449185 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term449 A K k s P) = (term449 A K k s P).
Proof. exact (MK_COMB (@lem4449183 K) (@lem4449182 A K k s P)). Qed.
Lemma lem4449186 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term449 A K k s P.
Proof. exact (EQ_MP (@lem4449185 A K k s P) (@lem4449101 A K k s P h1)). Qed.
Lemma lem4449206 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term461 A K k z s i) = (term461 A K k z s i).
Proof. exact (eq_refl (term461 A K k z s i)). Qed.
Lemma lem4449207 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term462 A K k z s) = (term462 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4449206 A K k z s i)). Qed.
Lemma lem4449208 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4449210 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term463 A K k z s) = (term463 A K k z s).
Proof. exact (MK_COMB (@lem4449208 K) (@lem4449207 A K k z s)). Qed.
Lemma lem4449211 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term463 A K k z s.
Proof. exact (EQ_MP (@lem4449210 A K k z s) (@lem4449163 A K z s i k h1)). Qed.
Lemma lem4449212 {A K : Type'} (_51392 : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term469 A K k s P _51392.
Proof. exact (@lem4449186 A K k s P h1 _51392). Qed.
Lemma lem4449213 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (_51392 : K) : (term469 A K k s P _51392) = (term447 A K k s P _51392).
Proof. exact (eq_refl (term469 A K k s P _51392)). Qed.
Lemma lem4449214 {A K : Type'} (_51392 : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term447 A K k s P _51392.
Proof. exact (EQ_MP (@lem4449213 A K k s P _51392) (@lem4449212 A K _51392 k s P h1)). Qed.
Lemma lem4449215 {A K : Type'} (_51392 : K) (_51393 : A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term470 A K k s P _51392 _51393.
Proof. exact (@lem4449214 A K _51392 k s P h1 _51393). Qed.
Lemma lem4449216 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (_51392 : K) (_51393 : A) : (term470 A K k s P _51392 _51393) = (term444 A K k s P _51392 _51393).
Proof. exact (eq_refl (term470 A K k s P _51392 _51393)). Qed.
Lemma lem4449217 {A K : Type'} (_51392 : K) (_51393 : A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term444 A K k s P _51392 _51393.
Proof. exact (EQ_MP (@lem4449216 A K k s P _51392 _51393) (@lem4449215 A K _51392 _51393 k s P h1)). Qed.
Lemma lem4449218 {A K : Type'} (_51394 : K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term471 A K k z s _51394.
Proof. exact (@lem4449211 A K z s i k h1 _51394). Qed.
Lemma lem4449219 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51394 : K) : (term471 A K k z s _51394) = (term461 A K k z s _51394).
Proof. exact (eq_refl (term471 A K k z s _51394)). Qed.
Lemma lem4449231 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (_51392 : K) (_51393 : A) : (term444 A K k s P _51392 _51393) = (term472 A K k s P _51392 _51393).
Proof. exact (@lem4448355 (term473 K _51392 k) (term474 A K _51393 s _51392) (P _51392 _51393)). Qed.
Lemma lem4449232 {A K : Type'} (_51392 : K) (_51393 : A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term472 A K k s P _51392 _51393.
Proof. exact (EQ_MP (@lem4449231 A K k s P _51392 _51393) (@lem4449217 A K _51392 _51393 k s P h1)). Qed.
Lemma lem4449234 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) (h1 : term321 A K P z i) : term468 A K P z i.
Proof. exact (EQ_MP (@lem4449159 A K P z i) (@lem4449067 A K P z i h1)). Qed.
Lemma lem4449244 {A K : Type'} (_51394 : K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term461 A K k z s _51394.
Proof. exact (EQ_MP (@lem4449219 A K k z s _51394) (@lem4449218 A K _51394 z s i k h1)). Qed.
Lemma lem4449246 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : @IN K i k.
Proof. exact (proj2 (@lem4449145 A K z s i k h1)). Qed.
Lemma lem4449247 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term475 K i k.
Proof. exact (fun h0 : term473 K i k => @lem4449246 A K z s i k h1). Qed.
Lemma lem4449249 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4449250 {K : Type'} (i : K) (k : K -> Prop) : (term475 K i k) = (@IN K i k).
Proof. exact (@lem4449249 (@IN K i k)). Qed.
Lemma lem4449251 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : @IN K i k.
Proof. exact (EQ_MP (@lem4449250 K i k) (@lem4449247 A K z s i k h1)). Qed.
Lemma lem4449253 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : @IN K i k.
Proof. exact (proj2 (@lem4449145 A K z s i k h1)). Qed.
Lemma lem4449254 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term475 K i k.
Proof. exact (fun h0 : term473 K i k => @lem4449253 A K z s i k h1). Qed.
Lemma lem4449256 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4449257 {K : Type'} (i : K) (k : K -> Prop) : (term475 K i k) = (@IN K i k).
Proof. exact (@lem4449256 (@IN K i k)). Qed.
Lemma lem4449258 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : @IN K i k.
Proof. exact (EQ_MP (@lem4449257 K i k) (@lem4449254 A K z s i k h1)). Qed.
Lemma lem4449264 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4449265 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51394 : K) (k : K -> Prop) : (term461 A K k z s _51394) = (term476 A K z s _51394 k).
Proof. exact (@lem4449264 (term459 A K z s _51394) (term473 K _51394 k)). Qed.
Lemma lem4449271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4449272 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51394 : K) (k : K -> Prop) : (term477 A K k z s _51394) = (term478 A K z s _51394 k).
Proof. exact (MK_COMB (@lem4449271) (@lem4449265 A K z s _51394 k)). Qed.
Lemma lem4449278 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51394 : K) (k : K -> Prop) : (term476 A K z s _51394 k) = (term476 A K z s _51394 k).
Proof. exact (eq_refl (term476 A K z s _51394 k)). Qed.
Lemma lem4449279 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51394 : K) (k : K -> Prop) : ((term461 A K k z s _51394) = (term476 A K z s _51394 k)) = ((term476 A K z s _51394 k) = (term476 A K z s _51394 k)).
Proof. exact (MK_COMB (@lem4449272 A K z s _51394 k) (@lem4449278 A K z s _51394 k)). Qed.
Lemma lem4449281 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4449282 (x : Prop) : (x = x) = True.
Proof. exact (@lem4449281 Prop x). Qed.
Lemma lem4449283 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51394 : K) (k : K -> Prop) : ((term476 A K z s _51394 k) = (term476 A K z s _51394 k)) = True.
Proof. exact (@lem4449282 (term476 A K z s _51394 k)). Qed.
Lemma lem4449284 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51394 : K) (k : K -> Prop) : ((term461 A K k z s _51394) = (term476 A K z s _51394 k)) = True.
Proof. exact (TRANS (@lem4449279 A K z s _51394 k) (@lem4449283 A K z s _51394 k)). Qed.
Lemma lem4449285 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51394 : K) (k : K -> Prop) : True = ((term461 A K k z s _51394) = (term476 A K z s _51394 k)).
Proof. exact (SYM (@lem4449284 A K z s _51394 k)). Qed.
Lemma lem4449286 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51394 : K) (k : K -> Prop) : (term461 A K k z s _51394) = (term476 A K z s _51394 k).
Proof. exact (EQ_MP (@lem4449285 A K z s _51394 k) (@lem0)). Qed.
Lemma lem4449287 {A K : Type'} (_51394 : K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term476 A K z s _51394 k.
Proof. exact (EQ_MP (@lem4449286 A K z s _51394 k) (@lem4449244 A K _51394 z s i k h1)). Qed.
Lemma lem4449289 (b : Prop) (a : Prop) : (a \/ b) = (term315 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4449290 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51394 : K) : (term476 A K z s _51394 k) = (term479 A K k z s _51394).
Proof. exact (@lem4449289 (term473 K _51394 k) (term459 A K z s _51394)). Qed.
Lemma lem4449292 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4449293 {K : Type'} (_51394 : K) (k : K -> Prop) : (term480 K _51394 k) = (@IN K _51394 k).
Proof. exact (@lem4449292 (@IN K _51394 k)). Qed.
Lemma lem4449294 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4449295 {K : Type'} (_51394 : K) (k : K -> Prop) : (term481 K _51394 k) = (term27 K _51394 k).
Proof. exact (MK_COMB (@lem4449294) (@lem4449293 K _51394 k)). Qed.
Lemma lem4449296 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51394 : K) : (term459 A K z s _51394) = (term459 A K z s _51394).
Proof. exact (eq_refl (term459 A K z s _51394)). Qed.
Lemma lem4449297 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51394 : K) : (term479 A K k z s _51394) = (term482 A K k z s _51394).
Proof. exact (MK_COMB (@lem4449295 K _51394 k) (@lem4449296 A K z s _51394)). Qed.
Lemma lem4449298 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51394 : K) : (term476 A K z s _51394 k) = (term482 A K k z s _51394).
Proof. exact (TRANS (@lem4449290 A K k z s _51394) (@lem4449297 A K k z s _51394)). Qed.
Lemma lem4449301 {A K : Type'} (_51394 : K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term482 A K k z s _51394.
Proof. exact (EQ_MP (@lem4449298 A K k z s _51394) (@lem4449287 A K _51394 z s i k h1)). Qed.
Lemma lem4449302 {A K : Type'} (_51394 : K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term482 A K k z s _51394.
Proof. exact (@lem4449301 A K _51394 z s i k h1). Qed.
Lemma lem4449303 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term482 A K k z s i.
Proof. exact (@lem4449302 A K i z s i k h1). Qed.
Lemma lem4449306 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term459 A K z s i.
Proof. exact (@lem4449303 A K z s i k h1 (@lem4449258 A K z s i k h1)). Qed.
Lemma lem4449307 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term483 A K z s i.
Proof. exact (fun h0 : term484 A K z s i => @lem4449306 A K z s i k h1). Qed.
Lemma lem4449309 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4449310 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) : (term483 A K z s i) = (term459 A K z s i).
Proof. exact (@lem4449309 (term459 A K z s i)). Qed.
Lemma lem4449311 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term459 A K z s i.
Proof. exact (EQ_MP (@lem4449310 A K z s i) (@lem4449307 A K z s i k h1)). Qed.
Lemma lem4449317 (q : Prop) (p : Prop) (r : Prop) : (term341 p q r) = (term341 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4449318 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (_51392 : K) (_51393 : A) : (term472 A K k s P _51392 _51393) = (term485 A K s k P _51392 _51393).
Proof. exact (@lem4449317 (term474 A K _51393 s _51392) (term473 K _51392 k) (P _51392 _51393)). Qed.
Lemma lem4449332 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4449333 {A K : Type'} (P : type1470 A K) (_51393 : A) (_51392 : K) (k : K -> Prop) : (term486 A K k P _51392 _51393) = (term487 A K P _51393 _51392 k).
Proof. exact (@lem4449332 (P _51392 _51393) (term473 K _51392 k)). Qed.
Lemma lem4449339 {A K : Type'} (_51393 : A) (s : type1470 A K) (_51392 : K) : (term488 A K _51393 s _51392) = (term488 A K _51393 s _51392).
Proof. exact (eq_refl (term488 A K _51393 s _51392)). Qed.
Lemma lem4449340 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (_51393 : A) (_51392 : K) (k : K -> Prop) : (term485 A K s k P _51392 _51393) = (term489 A K s P _51393 _51392 k).
Proof. exact (MK_COMB (@lem4449339 A K _51393 s _51392) (@lem4449333 A K P _51393 _51392 k)). Qed.
Lemma lem4449344 (q : Prop) (p : Prop) (r : Prop) : (term341 p q r) = (term341 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4449345 {A K : Type'} (P : type1470 A K) (_51393 : A) (s : type1470 A K) (_51392 : K) (k : K -> Prop) : (term489 A K s P _51393 _51392 k) = (term490 A K P _51393 s _51392 k).
Proof. exact (@lem4449344 (P _51392 _51393) (term474 A K _51393 s _51392) (term473 K _51392 k)). Qed.
Lemma lem4449361 {A K : Type'} (P : type1470 A K) (_51393 : A) (s : type1470 A K) (_51392 : K) (k : K -> Prop) : (term485 A K s k P _51392 _51393) = (term490 A K P _51393 s _51392 k).
Proof. exact (TRANS (@lem4449340 A K s P _51393 _51392 k) (@lem4449345 A K P _51393 s _51392 k)). Qed.
Lemma lem4449362 {A K : Type'} (P : type1470 A K) (_51393 : A) (s : type1470 A K) (_51392 : K) (k : K -> Prop) : (term472 A K k s P _51392 _51393) = (term490 A K P _51393 s _51392 k).
Proof. exact (TRANS (@lem4449318 A K s k P _51392 _51393) (@lem4449361 A K P _51393 s _51392 k)). Qed.
Lemma lem4449363 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4449364 {A K : Type'} (P : type1470 A K) (_51393 : A) (s : type1470 A K) (_51392 : K) (k : K -> Prop) : (term491 A K k s P _51392 _51393) = (term492 A K P _51393 s _51392 k).
Proof. exact (MK_COMB (@lem4449363) (@lem4449362 A K P _51393 s _51392 k)). Qed.
Lemma lem4449378 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4449379 {A K : Type'} (_51393 : A) (s : type1470 A K) (_51392 : K) (k : K -> Prop) : (term440 A K k _51393 s _51392) = (term493 A K _51393 s _51392 k).
Proof. exact (@lem4449378 (term474 A K _51393 s _51392) (term473 K _51392 k)). Qed.
Lemma lem4449385 {A K : Type'} (P : type1470 A K) (_51392 : K) (_51393 : A) : (term494 A K P _51392 _51393) = (term494 A K P _51392 _51393).
Proof. exact (eq_refl (term494 A K P _51392 _51393)). Qed.
Lemma lem4449386 {A K : Type'} (P : type1470 A K) (_51393 : A) (s : type1470 A K) (_51392 : K) (k : K -> Prop) : (term495 A K P k _51393 s _51392) = (term490 A K P _51393 s _51392 k).
Proof. exact (MK_COMB (@lem4449385 A K P _51392 _51393) (@lem4449379 A K _51393 s _51392 k)). Qed.
Lemma lem4449397 {A K : Type'} (P : type1470 A K) (_51393 : A) (s : type1470 A K) (_51392 : K) (k : K -> Prop) : ((term472 A K k s P _51392 _51393) = (term495 A K P k _51393 s _51392)) = ((term490 A K P _51393 s _51392 k) = (term490 A K P _51393 s _51392 k)).
Proof. exact (MK_COMB (@lem4449364 A K P _51393 s _51392 k) (@lem4449386 A K P _51393 s _51392 k)). Qed.
Lemma lem4449399 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4449400 (x : Prop) : (x = x) = True.
Proof. exact (@lem4449399 Prop x). Qed.
Lemma lem4449401 {A K : Type'} (P : type1470 A K) (_51393 : A) (s : type1470 A K) (_51392 : K) (k : K -> Prop) : ((term490 A K P _51393 s _51392 k) = (term490 A K P _51393 s _51392 k)) = True.
Proof. exact (@lem4449400 (term490 A K P _51393 s _51392 k)). Qed.
Lemma lem4449402 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (_51393 : A) (s : type1470 A K) (_51392 : K) : ((term472 A K k s P _51392 _51393) = (term495 A K P k _51393 s _51392)) = True.
Proof. exact (TRANS (@lem4449397 A K P _51393 s _51392 k) (@lem4449401 A K P _51393 s _51392 k)). Qed.
Lemma lem4449403 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (_51393 : A) (s : type1470 A K) (_51392 : K) : True = ((term472 A K k s P _51392 _51393) = (term495 A K P k _51393 s _51392)).
Proof. exact (SYM (@lem4449402 A K P k _51393 s _51392)). Qed.
Lemma lem4449404 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (_51393 : A) (s : type1470 A K) (_51392 : K) : (term472 A K k s P _51392 _51393) = (term495 A K P k _51393 s _51392).
Proof. exact (EQ_MP (@lem4449403 A K P k _51393 s _51392) (@lem0)). Qed.
Lemma lem4449405 {A K : Type'} (_51393 : A) (_51392 : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term495 A K P k _51393 s _51392.
Proof. exact (EQ_MP (@lem4449404 A K P k _51393 s _51392) (@lem4449232 A K _51392 _51393 k s P h1)). Qed.
Lemma lem4449407 (b : Prop) (a : Prop) : (a \/ b) = (term315 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4449408 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (_51392 : K) (_51393 : A) : (term495 A K P k _51393 s _51392) = (term496 A K k s P _51392 _51393).
Proof. exact (@lem4449407 (term440 A K k _51393 s _51392) (P _51392 _51393)). Qed.
Lemma lem4449410 (a : Prop) (b : Prop) : (term497 a b) = (term498 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4449411 {A K : Type'} (k : K -> Prop) (_51393 : A) (s : type1470 A K) (_51392 : K) : (term499 A K k _51393 s _51392) = (term500 A K k _51393 s _51392).
Proof. exact (@lem4449410 (term473 K _51392 k) (term474 A K _51393 s _51392)). Qed.
Lemma lem4449413 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4449414 {K : Type'} (_51392 : K) (k : K -> Prop) : (term480 K _51392 k) = (@IN K _51392 k).
Proof. exact (@lem4449413 (@IN K _51392 k)). Qed.
Lemma lem4449415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4449416 {K : Type'} (_51392 : K) (k : K -> Prop) : (term501 K _51392 k) = (term2 K _51392 k).
Proof. exact (MK_COMB (@lem4449415) (@lem4449414 K _51392 k)). Qed.
Lemma lem4449418 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4449419 {A K : Type'} (_51393 : A) (s : type1470 A K) (_51392 : K) : (term502 A K _51393 s _51392) = (term15 A K _51393 s _51392).
Proof. exact (@lem4449418 (term15 A K _51393 s _51392)). Qed.
Lemma lem4449420 {A K : Type'} (k : K -> Prop) (_51393 : A) (s : type1470 A K) (_51392 : K) : (term500 A K k _51393 s _51392) = (term445 A K k _51393 s _51392).
Proof. exact (MK_COMB (@lem4449416 K _51392 k) (@lem4449419 A K _51393 s _51392)). Qed.
Lemma lem4449421 {A K : Type'} (k : K -> Prop) (_51393 : A) (s : type1470 A K) (_51392 : K) : (term499 A K k _51393 s _51392) = (term445 A K k _51393 s _51392).
Proof. exact (TRANS (@lem4449411 A K k _51393 s _51392) (@lem4449420 A K k _51393 s _51392)). Qed.
Lemma lem4449422 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4449423 {A K : Type'} (k : K -> Prop) (_51393 : A) (s : type1470 A K) (_51392 : K) : (term503 A K k _51393 s _51392) = (term504 A K k _51393 s _51392).
Proof. exact (MK_COMB (@lem4449422) (@lem4449421 A K k _51393 s _51392)). Qed.
Lemma lem4449424 {A K : Type'} (P : type1470 A K) (_51392 : K) (_51393 : A) : (P _51392 _51393) = (P _51392 _51393).
Proof. exact (eq_refl (P _51392 _51393)). Qed.
Lemma lem4449425 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (_51392 : K) (_51393 : A) : (term496 A K k s P _51392 _51393) = (term433 A K k s P _51392 _51393).
Proof. exact (MK_COMB (@lem4449423 A K k _51393 s _51392) (@lem4449424 A K P _51392 _51393)). Qed.
Lemma lem4449426 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (_51392 : K) (_51393 : A) : (term495 A K P k _51393 s _51392) = (term433 A K k s P _51392 _51393).
Proof. exact (TRANS (@lem4449408 A K k s P _51392 _51393) (@lem4449425 A K k s P _51392 _51393)). Qed.
Lemma lem4449428 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term402 A K z s i k) : term505 A K k z s i.
Proof. exact (conj (@lem4449251 A K z s i k h1) (@lem4449311 A K z s i k h1)). Qed.
Lemma lem4449430 {A K : Type'} (_51392 : K) (_51393 : A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term433 A K k s P _51392 _51393.
Proof. exact (EQ_MP (@lem4449426 A K k s P _51392 _51393) (@lem4449405 A K _51393 _51392 k s P h1)). Qed.
Lemma lem4449431 {A K : Type'} (_51392 : K) (_51393 : A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term433 A K k s P _51392 _51393.
Proof. exact (@lem4449430 A K _51392 _51393 k s P h1). Qed.
Lemma lem4449432 {A K : Type'} (z : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term506 A K k s P z i.
Proof. exact (@lem4449431 A K i (@I (K -> A) z i) k s P h1). Qed.
Lemma lem4449435 {A K : Type'} (P : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term377 A K k s P) (h2 : term402 A K z s i k) : term467 A K P z i.
Proof. exact (@lem4449432 A K z i k s P h1 (@lem4449428 A K z s i k h2)). Qed.
Lemma lem4449436 {A K : Type'} (P : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term377 A K k s P) (h2 : term402 A K z s i k) : term507 A K P z i.
Proof. exact (fun h0 : term468 A K P z i => @lem4449435 A K P z s i k h1 h2). Qed.
Lemma lem4449438 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4449439 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) : (term507 A K P z i) = (term467 A K P z i).
Proof. exact (@lem4449438 (term467 A K P z i)). Qed.
Lemma lem4449440 {A K : Type'} (P : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term377 A K k s P) (h2 : term402 A K z s i k) : term467 A K P z i.
Proof. exact (EQ_MP (@lem4449439 A K P z i) (@lem4449436 A K P z s i k h1 h2)). Qed.
Lemma lem4449443 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4449445 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) : (term468 A K P z i) = (term508 A K P z i).
Proof. exact (@lem4449443 (term467 A K P z i)). Qed.
Lemma lem4449448 {A K : Type'} (P : type1470 A K) (z : K -> A) (i : K) (h1 : term321 A K P z i) : term508 A K P z i.
Proof. exact (EQ_MP (@lem4449445 A K P z i) (@lem4449234 A K P z i h1)). Qed.
Lemma lem4449451 {A K : Type'} (P : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term377 A K k s P) (h2 : term321 A K P z i) (h3 : term402 A K z s i k) : False.
Proof. exact (@lem4449448 A K P z i h2 (@lem4449440 A K P z s i k h1 h3)). Qed.
Lemma lem4449452 {A K : Type'} (P : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term377 A K k s P) (h2 : term321 A K P z i) (h3 : term402 A K z s i k) : term324.
Proof. exact (fun h0 : ~ False => @lem4449451 A K P z s i k h1 h2 h3). Qed.
Lemma lem4449454 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4449455 : term324 = False.
Proof. exact (@lem4449454 False). Qed.
Lemma lem4449456 {A K : Type'} (P : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term377 A K k s P) (h2 : term321 A K P z i) (h3 : term402 A K z s i k) : False.
Proof. exact (EQ_MP (@lem4449455) (@lem4449452 A K P z s i k h1 h2 h3)). Qed.
Lemma lem4449457 {A K : Type'} (P : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term377 A K k s P) (h2 : term321 A K P z i) (h3 : term402 A K z s i k) : (term321 A K P z i) = False.
Proof. exact (prop_ext (fun h4 : term321 A K P z i => @lem4449456 A K P z s i k h1 h2 h3) (fun h4 : False => @lem4449067 A K P z i h2)). Qed.
Lemma lem4449458 {A K : Type'} (P : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term377 A K k s P) (h2 : term321 A K P z i) (h3 : term402 A K z s i k) : False.
Proof. exact (EQ_MP (@lem4449457 A K P z s i k h1 h2 h3) (@lem4449067 A K P z i h2)). Qed.
Lemma lem4449459 {A K : Type'} (P : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term377 A K k s P) (h2 : term321 A K P z i) (h3 : term402 A K z s i k) : (term321 A K P z i) = False.
Proof. exact (prop_ext (fun h4 : term321 A K P z i => @lem4449458 A K P z s i k h1 h2 h3) (fun h4 : False => @lem4448914 A K P z i h2)). Qed.
Lemma lem4449460 {A K : Type'} (P : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term377 A K k s P) (h2 : term321 A K P z i) (h3 : term402 A K z s i k) : False.
Proof. exact (EQ_MP (@lem4449459 A K P z s i k h1 h2 h3) (@lem4448914 A K P z i h2)). Qed.
Lemma lem4449461 {A K : Type'} (P : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term377 A K k s P) (h2 : term402 A K z s i k) : term438 A K P z i.
Proof. exact (fun h0 : term321 A K P z i => @lem4449460 A K P z s i k h1 h0 h2). Qed.
Lemma lem4449462 {A K : Type'} (P : type1470 A K) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term377 A K k s P) (h2 : term402 A K z s i k) : term312 A K P z i.
Proof. exact (EQ_MP (@lem4448913 A K P z i) (@lem4449461 A K P z s i k h1 h2)). Qed.
Lemma lem4449463 {A K : Type'} (z : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term404 A K s k P z i.
Proof. exact (fun h0 : term402 A K z s i k => @lem4449462 A K P z s i k h1 h0). Qed.
Lemma lem4449468 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term406 A K s k P z.
Proof. exact (fun i : K => @lem4449463 A K z i k s P h1). Qed.
Lemma lem4449473 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) (h1 : term377 A K k s P) : term408 A K s k P.
Proof. exact (fun z : K -> A => @lem4449468 A K z k s P h1). Qed.
Lemma lem4449474 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : term410 A K s k P.
Proof. exact (fun h0 : term377 A K k s P => @lem4449473 A K k s P h0). Qed.
Lemma lem4449479 {A K : Type'} (k : K -> Prop) (P : type1470 A K) : term420 A K k P.
Proof. exact (fun s : type1470 A K => @lem4449474 A K s k P). Qed.
Lemma lem4449484 {A K : Type'} (P : type1470 A K) : term424 A K P.
Proof. exact (fun k : K -> Prop => @lem4449479 A K k P). Qed.
Lemma lem4449489 {A K : Type'} : term428 A K.
Proof. exact (fun P : type1470 A K => @lem4449484 A K P). Qed.
Lemma lem4449490 {A K : Type'} : term427 A K.
Proof. exact (EQ_MP (@lem4448907 A K) (@lem4449489 A K)). Qed.
Lemma lem4449491 {A K : Type'} (P : type1470 A K) : term509 A K P.
Proof. exact (@lem4449490 A K P). Qed.
Lemma lem4449492 {A K : Type'} (P : type1470 A K) : (term509 A K P) = (term423 A K P).
Proof. exact (eq_refl (term509 A K P)). Qed.
Lemma lem4449493 {A K : Type'} (P : type1470 A K) : term423 A K P.
Proof. exact (EQ_MP (@lem4449492 A K P) (@lem4449491 A K P)). Qed.
Lemma lem4449494 {A K : Type'} (P : type1470 A K) (k : K -> Prop) : term510 A K P k.
Proof. exact (@lem4449493 A K P k). Qed.
Lemma lem4449495 {A K : Type'} (k : K -> Prop) (P : type1470 A K) : (term510 A K P k) = (term419 A K k P).
Proof. exact (eq_refl (term510 A K P k)). Qed.
Lemma lem4449496 {A K : Type'} (k : K -> Prop) (P : type1470 A K) : term419 A K k P.
Proof. exact (EQ_MP (@lem4449495 A K k P) (@lem4449494 A K P k)). Qed.
Lemma lem4449497 {A K : Type'} (k : K -> Prop) (P : type1470 A K) (s : type1470 A K) : term511 A K k P s.
Proof. exact (@lem4449496 A K k P s). Qed.
Lemma lem4449498 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : (term511 A K k P s) = (term411 A K s k P).
Proof. exact (eq_refl (term511 A K k P s)). Qed.
Lemma lem4449499 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : term411 A K s k P.
Proof. exact (EQ_MP (@lem4449498 A K s k P) (@lem4449497 A K k P s)). Qed.
Lemma lem4449501 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : term411 A K s k P.
Proof. exact (@lem4448710 A K s k P (@lem4449499 A K s k P)). Qed.
Lemma lem4449502 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term412 A K s k P) : False.
Proof. exact (@lem4449501 A K s k P (@lem4448694 A K s k P h1)). Qed.
Lemma lem4449503 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term412 A K s k P) : (term412 A K s k P) = False.
Proof. exact (prop_ext (fun h2 : term412 A K s k P => @lem4449502 A K s k P h1) (fun h2 : False => @lem4448694 A K s k P h1)). Qed.
Lemma lem4449504 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term412 A K s k P) : False.
Proof. exact (EQ_MP (@lem4449503 A K s k P h1) (@lem4448694 A K s k P h1)). Qed.
Lemma lem4449505 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : term411 A K s k P.
Proof. exact (fun h0 : term412 A K s k P => @lem4449504 A K s k P h0). Qed.
Lemma lem4449506 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) : term410 A K s k P.
Proof. exact (EQ_MP (@lem4448693 A K s k P) (@lem4449505 A K s k P)). Qed.
Lemma lem4449508 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term7 A K k s).
Proof. exact (EQ_MP (@lem4448344 A K k s) (@lem4448343 A K k s)). Qed.
Lemma lem4449509 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term7 A K k s).
Proof. exact (@lem4449508 A K k s). Qed.
Lemma lem4449510 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4449511 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term354 A K k s) = (term9 A K k s).
Proof. exact (MK_COMB (@lem4449510) (@lem4449509 A K k s)). Qed.
Lemma lem4449512 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : term9 A K k s.
Proof. exact (EQ_MP (@lem4449511 A K k s) (@lem4448404 A K k s h1)). Qed.
Lemma lem4449516 {_106676 _106693 : Type'} (k : _106693 -> Prop) (s : type1470 _106676 _106693) : (term9 _106676 _106693 k s) = (term13 _106676 _106693 k s).
Proof. exact (EQ_MP (@lem4447035 _106676 _106693 k s) (@lem4448329 _106676 _106693 k s)). Qed.
Lemma lem4449517 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term9 A K k s) = (term13 A K k s).
Proof. exact (@lem4449516 A K k s). Qed.
Lemma lem4449519 {A B : Type'} (P : type1413 A B) : (term164 A B P) = (term165 A B P).
Proof. exact (EQ_MP (@lem4448338 A B P) (@lem4448337 A B P)). Qed.
Lemma lem4449520 {A K : Type'} (P : type1470 A K) : (term166 A K P) = (term167 A K P).
Proof. exact (@lem4449519 K A P). Qed.
Lemma lem4449521 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term512 A K k s) = (term513 A K k s).
Proof. exact (@lem4449520 A K (term514 A K k s)). Qed.
Lemma lem4449522 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term515 A K k s i) = (term31 A K k s i).
Proof. exact (eq_refl (term515 A K k s i)). Qed.
Lemma lem4449523 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4449524 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (x : A) : (term516 A K k s i x) = (term517 A K k s i x).
Proof. exact (MK_COMB (@lem4449522 A K k s i) (@lem4449523 A x)). Qed.
Lemma lem4449525 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term517 A K k s i x) = (term29 A K k x s i).
Proof. exact (eq_refl (term517 A K k s i x)). Qed.
Lemma lem4449526 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) : (term516 A K k s i x) = (term29 A K k x s i).
Proof. exact (TRANS (@lem4449524 A K k s i x) (@lem4449525 A K k x s i)). Qed.
Lemma lem4449527 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term518 A K k s i) = (term31 A K k s i).
Proof. exact (fun_ext (fun x : A => @lem4449526 A K k x s i)). Qed.
Lemma lem4449528 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4449529 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term519 A K k s i) = (term33 A K k s i).
Proof. exact (MK_COMB (@lem4449528 A) (@lem4449527 A K k s i)). Qed.
Lemma lem4449530 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term520 A K k s) = (term35 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4449529 A K k s i)). Qed.
Lemma lem4449531 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4449532 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term512 A K k s) = (term13 A K k s).
Proof. exact (MK_COMB (@lem4449531 K) (@lem4449530 A K k s)). Qed.
Lemma lem4449533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4449534 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term521 A K k s) = (term522 A K k s).
Proof. exact (MK_COMB (@lem4449533) (@lem4449532 A K k s)). Qed.
Lemma lem4449535 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term515 A K k s i) = (term31 A K k s i).
Proof. exact (eq_refl (term515 A K k s i)). Qed.
Lemma lem4449536 {A K : Type'} (x : K -> A) (i : K) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem4449537 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term523 A K k s x i) = (term524 A K k s x i).
Proof. exact (MK_COMB (@lem4449535 A K k s i) (@lem4449536 A K x i)). Qed.
Lemma lem4449538 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term524 A K k s x i) = (term429 A K k x s i).
Proof. exact (eq_refl (term524 A K k s x i)). Qed.
Lemma lem4449539 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term523 A K k s x i) = (term429 A K k x s i).
Proof. exact (TRANS (@lem4449537 A K k s x i) (@lem4449538 A K k x s i)). Qed.
Lemma lem4449540 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term525 A K k s x) = (term430 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4449539 A K k x s i)). Qed.
Lemma lem4449541 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4449542 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term526 A K k s x) = (term431 A K k x s).
Proof. exact (MK_COMB (@lem4449541 K) (@lem4449540 A K k x s)). Qed.
Lemma lem4449543 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term527 A K k s) = (term528 A K k s).
Proof. exact (fun_ext (fun x : K -> A => @lem4449542 A K k x s)). Qed.
Lemma lem4449544 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4449545 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term513 A K k s) = (term529 A K k s).
Proof. exact (MK_COMB (@lem4449544 A K) (@lem4449543 A K k s)). Qed.
Lemma lem4449546 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term512 A K k s) = (term513 A K k s)) = ((term13 A K k s) = (term529 A K k s)).
Proof. exact (MK_COMB (@lem4449534 A K k s) (@lem4449545 A K k s)). Qed.
Lemma lem4449547 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term13 A K k s) = (term529 A K k s).
Proof. exact (EQ_MP (@lem4449546 A K k s) (@lem4449521 A K k s)). Qed.
Lemma lem4449552 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term9 A K k s) = (term529 A K k s).
Proof. exact (TRANS (@lem4449517 A K k s) (@lem4449547 A K k s)). Qed.
Lemma lem4449559 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4449560 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term530 A K k s) = (term531 A K k s).
Proof. exact (MK_COMB (@lem4449559) (@lem4449552 A K k s)). Qed.
Lemma lem4449573 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term377 A K k s P) = (term377 A K k s P).
Proof. exact (eq_refl (term377 A K k s P)). Qed.
Lemma lem4449574 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term532 A K k s P) = (term533 A K k s P).
Proof. exact (MK_COMB (@lem4449560 A K k s) (@lem4449573 A K k s P)). Qed.
Lemma lem4449576 {A : Type'} (P : A -> Prop) (Q : Prop) : (term330 A P Q) = (term331 A P Q).
Proof. exact (EQ_MP (@lem4448335 A P Q) (@lem4448334 A P Q)). Qed.
Lemma lem4449577 {A K : Type'} (P : type805 A K) (Q : Prop) : (term534 A K P Q) = (term535 A K P Q).
Proof. exact (@lem4449576 (K -> A) P Q). Qed.
Lemma lem4449578 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term536 A K k s P) = (term537 A K k s P).
Proof. exact (@lem4449577 A K (term528 A K k s) (term377 A K k s P)). Qed.
Lemma lem4449579 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term538 A K k s x) = (term431 A K k x s).
Proof. exact (eq_refl (term538 A K k s x)). Qed.
Lemma lem4449580 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term539 A K k s) = (term528 A K k s).
Proof. exact (fun_ext (fun x : K -> A => @lem4449579 A K k x s)). Qed.
Lemma lem4449581 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4449582 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term540 A K k s) = (term529 A K k s).
Proof. exact (MK_COMB (@lem4449581 A K) (@lem4449580 A K k s)). Qed.
Lemma lem4449583 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4449584 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term541 A K k s) = (term531 A K k s).
Proof. exact (MK_COMB (@lem4449583) (@lem4449582 A K k s)). Qed.
Lemma lem4449585 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term377 A K k s P) = (term377 A K k s P).
Proof. exact (eq_refl (term377 A K k s P)). Qed.
Lemma lem4449586 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term536 A K k s P) = (term533 A K k s P).
Proof. exact (MK_COMB (@lem4449584 A K k s) (@lem4449585 A K k s P)). Qed.
Lemma lem4449587 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4449588 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term542 A K k s P) = (term543 A K k s P).
Proof. exact (MK_COMB (@lem4449587) (@lem4449586 A K k s P)). Qed.
Lemma lem4449589 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term538 A K k s x) = (term431 A K k x s).
Proof. exact (eq_refl (term538 A K k s x)). Qed.
Lemma lem4449590 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4449591 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term544 A K k s x) = (term545 A K k x s).
Proof. exact (MK_COMB (@lem4449590) (@lem4449589 A K k x s)). Qed.
Lemma lem4449592 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term377 A K k s P) = (term377 A K k s P).
Proof. exact (eq_refl (term377 A K k s P)). Qed.
Lemma lem4449593 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term546 A K x k s P) = (term547 A K x k s P).
Proof. exact (MK_COMB (@lem4449591 A K k x s) (@lem4449592 A K k s P)). Qed.
Lemma lem4449594 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term548 A K k s P) = (term549 A K k s P).
Proof. exact (fun_ext (fun x : K -> A => @lem4449593 A K x k s P)). Qed.
Lemma lem4449595 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4449596 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term537 A K k s P) = (term550 A K k s P).
Proof. exact (MK_COMB (@lem4449595 A K) (@lem4449594 A K k s P)). Qed.
Lemma lem4449597 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : ((term536 A K k s P) = (term537 A K k s P)) = ((term533 A K k s P) = (term550 A K k s P)).
Proof. exact (MK_COMB (@lem4449588 A K k s P) (@lem4449596 A K k s P)). Qed.
Lemma lem4449598 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term533 A K k s P) = (term550 A K k s P).
Proof. exact (EQ_MP (@lem4449597 A K k s P) (@lem4449578 A K k s P)). Qed.
Lemma lem4449623 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term532 A K k s P) = (term550 A K k s P).
Proof. exact (TRANS (@lem4449574 A K k s P) (@lem4449598 A K k s P)). Qed.
Lemma lem4449624 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term550 A K k s P) = (term532 A K k s P).
Proof. exact (SYM (@lem4449623 A K k s P)). Qed.
Lemma lem4449625 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term431 A K k z s) : term431 A K k z s.
Proof. exact (h1). Qed.
Lemma lem4449626 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (h1 : term445 A K k x s i) : term445 A K k x s i.
Proof. exact (h1). Qed.
Lemma lem4449627 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term15 A K x s i) : term15 A K x s i.
Proof. exact (h1). Qed.
Lemma lem4449628 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4449629 {A K : Type'} (i : K) (x : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term408 A K s k P) : term551 A K s P i x k z.
Proof. exact (@lem4448689 A K s k P h1 (term552 A K i x k z)). Qed.
Lemma lem4449630 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term551 A K s P i x k z) = (term553 A K s P i x k z).
Proof. exact (eq_refl (term551 A K s P i x k z)). Qed.
Lemma lem4449631 {A K : Type'} (i : K) (x : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term408 A K s k P) : term553 A K s P i x k z.
Proof. exact (EQ_MP (@lem4449630 A K s P i x k z) (@lem4449629 A K i x z s k P h1)). Qed.
Lemma lem4449632 {A K : Type'} (x : A) (z : K -> A) (i : K) (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term408 A K s k P) : term554 A K s P x k z i.
Proof. exact (@lem4449631 A K i x z s k P h1 i). Qed.
Lemma lem4449633 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (term554 A K s P x k z i) = (term555 A K s P x k z i).
Proof. exact (eq_refl (term554 A K s P x k z i)). Qed.
Lemma lem4449634 {A K : Type'} (x : A) (z : K -> A) (i : K) (s : type1470 A K) (k : K -> Prop) (P : type1470 A K) (h1 : term408 A K s k P) : term555 A K s P x k z i.
Proof. exact (EQ_MP (@lem4449633 A K s P x k z i) (@lem4449632 A K x z i s k P h1)). Qed.
Lemma lem4449645 {_83152 : Type'} : term556 _83152.
Proof. exact (EQ_MP (@lem3184717 _83152) (@lem3184714 _83152)). Qed.
Lemma lem4449646 {_83152 : Type'} (p : _83152 -> Prop) : term557 _83152 p.
Proof. exact (@lem4449645 _83152 p). Qed.
Lemma lem4449647 {_83152 : Type'} (p : _83152 -> Prop) : (term557 _83152 p) = (term558 _83152 p).
Proof. exact (eq_refl (term557 _83152 p)). Qed.
Lemma lem4449648 {_83152 : Type'} (p : _83152 -> Prop) : term558 _83152 p.
Proof. exact (EQ_MP (@lem4449647 _83152 p) (@lem4449646 _83152 p)). Qed.
Lemma lem4449649 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term559 _83152 p x.
Proof. exact (@lem4449648 _83152 p x). Qed.
Lemma lem4449650 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term559 _83152 p x) = ((term560 _83152 p x) = (p x)).
Proof. exact (eq_refl (term559 _83152 p x)). Qed.
Lemma lem4449673 {A B : Type'} (s : A -> Prop) : term561 A B s.
Proof. exact (@lem4382798 A B s). Qed.
Lemma lem4449674 {A B : Type'} (s : A -> Prop) : (term561 A B s) = ((@EXTENSIONAL A B s) = (term562 A B s)).
Proof. exact (eq_refl (term561 A B s)). Qed.
Lemma lem4449694 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = ((@IN K i k) = True).
Proof. exact (@lem7 (@IN K i k)). Qed.
Lemma lem4449707 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term562 A B s).
Proof. exact (EQ_MP (@lem4449674 A B s) (@lem4449673 A B s)). Qed.
Lemma lem4449708 {A K : Type'} (s : K -> Prop) : (@EXTENSIONAL K A s) = (term563 A K s).
Proof. exact (@lem4449707 K A s). Qed.
Lemma lem4449709 {A K : Type'} (k : K -> Prop) : (@EXTENSIONAL K A k) = (term563 A K k).
Proof. exact (@lem4449708 A K k). Qed.
Lemma lem4449726 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term552 A K i x k z) = (term552 A K i x k z).
Proof. exact (eq_refl (term552 A K i x k z)). Qed.
Lemma lem4449727 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term564 A K i x k z) = (term565 A K i x k z).
Proof. exact (MK_COMB (@lem4449709 A K k) (@lem4449726 A K i x k z)). Qed.
Lemma lem4449729 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term560 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4449650 _83152 p x) (@lem4449649 _83152 p x)). Qed.
Lemma lem4449730 {A K : Type'} (p : type805 A K) (x : K -> A) : (term566 A K p x) = (p x).
Proof. exact (@lem4449729 (K -> A) p x). Qed.
Lemma lem4449731 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term567 A K i x k z) = (term568 A K i x k z).
Proof. exact (@lem4449730 A K (term569 A K k) (term552 A K i x k z)). Qed.
Lemma lem4449732 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term570 A K k f) = (term571 A K k f).
Proof. exact (eq_refl (term570 A K k f)). Qed.
Lemma lem4449733 {A K : Type'} (GEN_PVAR_139 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_139) = (@SETSPEC (K -> A) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_139)). Qed.
Lemma lem4449734 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term572 A K GEN_PVAR_139 k f) = (term573 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4449733 A K GEN_PVAR_139) (@lem4449732 A K k f)). Qed.
Lemma lem4449735 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4449736 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term574 A K GEN_PVAR_139 k f) = (term575 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4449734 A K GEN_PVAR_139 k f) (@lem4449735 A K f)). Qed.
Lemma lem4449737 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term576 A K GEN_PVAR_139 k) = (term577 A K GEN_PVAR_139 k).
Proof. exact (fun_ext (fun f : K -> A => @lem4449736 A K GEN_PVAR_139 k f)). Qed.
Lemma lem4449738 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4449739 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term578 A K GEN_PVAR_139 k) = (term579 A K GEN_PVAR_139 k).
Proof. exact (MK_COMB (@lem4449738 A K) (@lem4449737 A K GEN_PVAR_139 k)). Qed.
Lemma lem4449740 {A K : Type'} (k : K -> Prop) : (term580 A K k) = (term581 A K k).
Proof. exact (fun_ext (fun GEN_PVAR_139 : K -> A => @lem4449739 A K GEN_PVAR_139 k)). Qed.
Lemma lem4449741 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4449742 {A K : Type'} (k : K -> Prop) : (term582 A K k) = (term563 A K k).
Proof. exact (MK_COMB (@lem4449741 A K) (@lem4449740 A K k)). Qed.
Lemma lem4449743 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term552 A K i x k z) = (term552 A K i x k z).
Proof. exact (eq_refl (term552 A K i x k z)). Qed.
Lemma lem4449744 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term567 A K i x k z) = (term565 A K i x k z).
Proof. exact (MK_COMB (@lem4449742 A K k) (@lem4449743 A K i x k z)). Qed.
Lemma lem4449745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4449746 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term583 A K i x k z) = (term584 A K i x k z).
Proof. exact (MK_COMB (@lem4449745) (@lem4449744 A K i x k z)). Qed.
Lemma lem4449747 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term568 A K i x k z) = (term585 A K i x k z).
Proof. exact (eq_refl (term568 A K i x k z)). Qed.
Lemma lem4449748 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : ((term567 A K i x k z) = (term568 A K i x k z)) = ((term565 A K i x k z) = (term585 A K i x k z)).
Proof. exact (MK_COMB (@lem4449746 A K i x k z) (@lem4449747 A K i x k z)). Qed.
Lemma lem4449749 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term565 A K i x k z) = (term585 A K i x k z).
Proof. exact (EQ_MP (@lem4449748 A K i x k z) (@lem4449731 A K i x k z)). Qed.
Lemma lem4449759 {A B : Type'} (f : A -> B) (y : A) : (term586 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4449760 {A K : Type'} (f : K -> A) (y : K) : (term587 A K f y) = (f y).
Proof. exact (@lem4449759 K A f y). Qed.
Lemma lem4449761 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (x' : K) : (term588 A K i x k z x') = (term589 A K i x k z x').
Proof. exact (@lem4449760 A K (term552 A K i x k z) x'). Qed.
Lemma lem4449762 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (j : K) : (term589 A K i x k z j) = (term590 A K i x k z j).
Proof. exact (eq_refl (term589 A K i x k z j)). Qed.
Lemma lem4449763 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term591 A K i x k z) = (term552 A K i x k z).
Proof. exact (fun_ext (fun j : K => @lem4449762 A K i x k z j)). Qed.
Lemma lem4449764 {K : Type'} (x : K) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4449765 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (x' : K) : (term588 A K i x k z x') = (term589 A K i x k z x').
Proof. exact (MK_COMB (@lem4449763 A K i x k z) (@lem4449764 K x')). Qed.
Lemma lem4449766 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4449767 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (x' : K) : (term592 A K i x k z x') = (term593 A K i x k z x').
Proof. exact (MK_COMB (@lem4449766 A) (@lem4449765 A K i x k z x')). Qed.
Lemma lem4449768 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (x' : K) : (term589 A K i x k z x') = (term590 A K i x k z x').
Proof. exact (eq_refl (term589 A K i x k z x')). Qed.
Lemma lem4449769 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (x' : K) : ((term588 A K i x k z x') = (term589 A K i x k z x')) = ((term589 A K i x k z x') = (term590 A K i x k z x')).
Proof. exact (MK_COMB (@lem4449767 A K i x k z x') (@lem4449768 A K i x k z x')). Qed.
Lemma lem4449770 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (x' : K) : (term589 A K i x k z x') = (term590 A K i x k z x').
Proof. exact (EQ_MP (@lem4449769 A K i x k z x') (@lem4449761 A K i x k z x')). Qed.
Lemma lem4449775 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4449776 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (x' : K) : (term593 A K i x k z x') = (term594 A K i x k z x').
Proof. exact (MK_COMB (@lem4449775 A) (@lem4449770 A K i x k z x')). Qed.
Lemma lem4449777 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4449778 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (x' : K) : ((term589 A K i x k z x') = (@ARB A)) = ((term590 A K i x k z x') = (@ARB A)).
Proof. exact (MK_COMB (@lem4449776 A K i x k z x') (@lem4449777 A)). Qed.
Lemma lem4449781 {K : Type'} (x : K) (k : K -> Prop) : (term595 K x k) = (term595 K x k).
Proof. exact (eq_refl (term595 K x k)). Qed.
Lemma lem4449782 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (x' : K) : (term596 A K i x k z x') = (term597 A K i x k z x').
Proof. exact (MK_COMB (@lem4449781 K x' k) (@lem4449778 A K i x k z x')). Qed.
Lemma lem4449785 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term598 A K i x k z) = (term599 A K i x k z).
Proof. exact (fun_ext (fun x' : K => @lem4449782 A K i x k z x')). Qed.
Lemma lem4449786 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4449787 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term585 A K i x k z) = (term600 A K i x k z).
Proof. exact (MK_COMB (@lem4449786 K) (@lem4449785 A K i x k z)). Qed.
Lemma lem4449792 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term565 A K i x k z) = (term600 A K i x k z).
Proof. exact (TRANS (@lem4449749 A K i x k z) (@lem4449787 A K i x k z)). Qed.
Lemma lem4449793 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term564 A K i x k z) = (term600 A K i x k z).
Proof. exact (TRANS (@lem4449727 A K i x k z) (@lem4449792 A K i x k z)). Qed.
Lemma lem4449794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4449795 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term601 A K i x k z) = (term602 A K i x k z).
Proof. exact (MK_COMB (@lem4449794) (@lem4449793 A K i x k z)). Qed.
Lemma lem4449803 {A B : Type'} (f : A -> B) (y : A) : (term586 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4449804 {A K : Type'} (f : K -> A) (y : K) : (term587 A K f y) = (f y).
Proof. exact (@lem4449803 K A f y). Qed.
Lemma lem4449805 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term588 A K i x k z i') = (term589 A K i x k z i').
Proof. exact (@lem4449804 A K (term552 A K i x k z) i'). Qed.
Lemma lem4449806 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (j : K) : (term589 A K i x k z j) = (term590 A K i x k z j).
Proof. exact (eq_refl (term589 A K i x k z j)). Qed.
Lemma lem4449807 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term591 A K i x k z) = (term552 A K i x k z).
Proof. exact (fun_ext (fun j : K => @lem4449806 A K i x k z j)). Qed.
Lemma lem4449808 {K : Type'} (i' : K) : i' = i'.
Proof. exact (eq_refl i'). Qed.
Lemma lem4449809 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term588 A K i x k z i') = (term589 A K i x k z i').
Proof. exact (MK_COMB (@lem4449807 A K i x k z) (@lem4449808 K i')). Qed.
Lemma lem4449810 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4449811 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term592 A K i x k z i') = (term593 A K i x k z i').
Proof. exact (MK_COMB (@lem4449810 A) (@lem4449809 A K i x k z i')). Qed.
Lemma lem4449812 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term589 A K i x k z i') = (term590 A K i x k z i').
Proof. exact (eq_refl (term589 A K i x k z i')). Qed.
Lemma lem4449813 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : ((term588 A K i x k z i') = (term589 A K i x k z i')) = ((term589 A K i x k z i') = (term590 A K i x k z i')).
Proof. exact (MK_COMB (@lem4449811 A K i x k z i') (@lem4449812 A K i x k z i')). Qed.
Lemma lem4449814 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term589 A K i x k z i') = (term590 A K i x k z i').
Proof. exact (EQ_MP (@lem4449813 A K i x k z i') (@lem4449805 A K i x k z i')). Qed.
Lemma lem4449819 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4449820 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term603 A K i x k z i') = (term604 A K i x k z i').
Proof. exact (MK_COMB (@lem4449819 A) (@lem4449814 A K i x k z i')). Qed.
Lemma lem4449821 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4449822 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term605 A K i x k z s i') = (term606 A K i x k z s i').
Proof. exact (MK_COMB (@lem4449820 A K i x k z i') (@lem4449821 A K s i')). Qed.
Lemma lem4449823 {K : Type'} (i' : K) (k : K -> Prop) : (term27 K i' k) = (term27 K i' k).
Proof. exact (eq_refl (term27 K i' k)). Qed.
Lemma lem4449824 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term607 A K i x k z s i') = (term608 A K i x k z s i').
Proof. exact (MK_COMB (@lem4449823 K i' k) (@lem4449822 A K i x k z s i')). Qed.
Lemma lem4449827 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term609 A K i x k z s) = (term610 A K i x k z s).
Proof. exact (fun_ext (fun i' : K => @lem4449824 A K i x k z s i')). Qed.
Lemma lem4449828 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4449829 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term611 A K i x k z s) = (term612 A K i x k z s).
Proof. exact (MK_COMB (@lem4449828 K) (@lem4449827 A K i x k z s)). Qed.
Lemma lem4449834 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term613 A K i x k z s) = (term614 A K i x k z s).
Proof. exact (MK_COMB (@lem4449795 A K i x k z) (@lem4449829 A K i x k z s)). Qed.
Lemma lem4449837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4449838 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term615 A K i x k z s) = (term616 A K i x k z s).
Proof. exact (MK_COMB (@lem4449837) (@lem4449834 A K i x k z s)). Qed.
Lemma lem4449840 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (@IN K i k) = True.
Proof. exact (EQ_MP (@lem4449694 K i k) (@lem4449628 K i k h1)). Qed.
Lemma lem4449841 {A K : Type'} (x : A) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term617 A K x z s i k) = (term618 A K i x k z s).
Proof. exact (MK_COMB (@lem4449838 A K i x k z s) (@lem4449840 K i k h1)). Qed.
Lemma lem4449843 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4449844 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term618 A K i x k z s) = (term614 A K i x k z s).
Proof. exact (@lem4449843 (term614 A K i x k z s)). Qed.
Lemma lem4449869 {A K : Type'} (x : A) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term617 A K x z s i k) = (term614 A K i x k z s).
Proof. exact (TRANS (@lem4449841 A K x z s i k h1) (@lem4449844 A K i x k z s)). Qed.
Lemma lem4449870 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4449871 {A K : Type'} (x : A) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term619 A K x z s i k) = (term620 A K i x k z s).
Proof. exact (MK_COMB (@lem4449870) (@lem4449869 A K x z s i k h1)). Qed.
Lemma lem4449873 {A B : Type'} (f : A -> B) (y : A) : (term586 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4449874 {A K : Type'} (f : K -> A) (y : K) : (term587 A K f y) = (f y).
Proof. exact (@lem4449873 K A f y). Qed.
Lemma lem4449875 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (term621 A K x k z i) = (term622 A K x k z i).
Proof. exact (@lem4449874 A K (term552 A K i x k z) i). Qed.
Lemma lem4449876 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (j : K) : (term589 A K i x k z j) = (term590 A K i x k z j).
Proof. exact (eq_refl (term589 A K i x k z j)). Qed.
Lemma lem4449877 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term591 A K i x k z) = (term552 A K i x k z).
Proof. exact (fun_ext (fun j : K => @lem4449876 A K i x k z j)). Qed.
Lemma lem4449878 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4449879 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (term621 A K x k z i) = (term622 A K x k z i).
Proof. exact (MK_COMB (@lem4449877 A K i x k z) (@lem4449878 K i)). Qed.
Lemma lem4449880 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4449881 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (term623 A K x k z i) = (term624 A K x k z i).
Proof. exact (MK_COMB (@lem4449880 A) (@lem4449879 A K x k z i)). Qed.
Lemma lem4449882 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (term622 A K x k z i) = (term625 A K x k z i).
Proof. exact (eq_refl (term622 A K x k z i)). Qed.
Lemma lem4449883 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : ((term621 A K x k z i) = (term622 A K x k z i)) = ((term622 A K x k z i) = (term625 A K x k z i)).
Proof. exact (MK_COMB (@lem4449881 A K x k z i) (@lem4449882 A K x k z i)). Qed.
Lemma lem4449884 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (term622 A K x k z i) = (term625 A K x k z i).
Proof. exact (EQ_MP (@lem4449883 A K x k z i) (@lem4449875 A K x k z i)). Qed.
Lemma lem4449886 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term626 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem4449887 {A K : Type'} (x : K) (z : A) (y : A) : (term626 A K x y z) = y.
Proof. exact (@lem4449886 A K x z y). Qed.
Lemma lem4449888 {A K : Type'} (k : K -> Prop) (z : K -> A) (i : K) (x : A) : (term625 A K x k z i) = x.
Proof. exact (@lem4449887 A K i (term627 A K k z i) x). Qed.
Lemma lem4449889 {A K : Type'} (k : K -> Prop) (z : K -> A) (i : K) (x : A) : (term622 A K x k z i) = x.
Proof. exact (TRANS (@lem4449884 A K x k z i) (@lem4449888 A K k z i x)). Qed.
Lemma lem4449890 {A K : Type'} (P : type1470 A K) (i : K) : (P i) = (P i).
Proof. exact (eq_refl (P i)). Qed.
Lemma lem4449891 {A K : Type'} (k : K -> Prop) (z : K -> A) (P : type1470 A K) (i : K) (x : A) : (term628 A K P x k z i) = (P i x).
Proof. exact (MK_COMB (@lem4449890 A K P i) (@lem4449889 A K k z i x)). Qed.
Lemma lem4449892 {A K : Type'} (z : K -> A) (s : type1470 A K) (P : type1470 A K) (x : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term555 A K s P x k z i) = (term629 A K k z s P i x).
Proof. exact (MK_COMB (@lem4449871 A K x z s i k h1) (@lem4449891 A K k z P i x)). Qed.
Lemma lem4449895 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4449896 {A K : Type'} (z : K -> A) (s : type1470 A K) (P : type1470 A K) (x : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term630 A K s P x k z i) = (term631 A K k z s P i x).
Proof. exact (MK_COMB (@lem4449895) (@lem4449892 A K z s P x i k h1)). Qed.
Lemma lem4449897 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (P i x) = (P i x).
Proof. exact (eq_refl (P i x)). Qed.
Lemma lem4449898 {A K : Type'} (z : K -> A) (s : type1470 A K) (P : type1470 A K) (x : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term632 A K s k z P i x) = (term633 A K k z s P i x).
Proof. exact (MK_COMB (@lem4449896 A K z s P x i k h1) (@lem4449897 A K P i x)). Qed.
Lemma lem4449901 {A K : Type'} (s : type1470 A K) (z : K -> A) (P : type1470 A K) (x : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term633 A K k z s P i x) = (term632 A K s k z P i x).
Proof. exact (SYM (@lem4449898 A K z s P x i k h1)). Qed.
Lemma lem4449903 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4449904 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term633 A K k z s P i x) = (term634 A K k z s P i x).
Proof. exact (@lem4449903 (term633 A K k z s P i x)). Qed.
Lemma lem4449905 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term634 A K k z s P i x) = (term633 A K k z s P i x).
Proof. exact (SYM (@lem4449904 A K k z s P i x)). Qed.
Lemma lem4449906 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (h1 : term635 A K k z s P i x) : term635 A K k z s P i x.
Proof. exact (h1). Qed.
Lemma lem4449909 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (h1 : term636 A K k z s P i x) : term636 A K k z s P i x.
Proof. exact (h1). Qed.
Lemma lem4449910 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : term637 A K k z s P i x.
Proof. exact (fun h0 : term636 A K k z s P i x => @lem4449909 A K k z s P i x h0). Qed.
Lemma lem4449911 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (h1 : term637 A K k z s P i x) : term637 A K k z s P i x.
Proof. exact (h1). Qed.
Lemma lem4449912 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (h1 : term636 A K k z s P i x) : term636 A K k z s P i x.
Proof. exact (h1). Qed.
Lemma lem4449913 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (h1 : term636 A K k z s P i x) (h2 : term637 A K k z s P i x) : term636 A K k z s P i x.
Proof. exact (@lem4449911 A K k z s P i x h2 (@lem4449912 A K k z s P i x h1)). Qed.
Lemma lem4449914 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (h1 : term636 A K k z s P i x) : term638 A K k z s P i x.
Proof. exact (fun h0 : term637 A K k z s P i x => @lem4449913 A K k z s P i x h1 h0). Qed.
Lemma lem4449915 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (h1 : term637 A K k z s P i x) : term637 A K k z s P i x.
Proof. exact (h1). Qed.
Lemma lem4449916 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (h1 : term636 A K k z s P i x) (h2 : term637 A K k z s P i x) : term636 A K k z s P i x.
Proof. exact (@lem4449914 A K k z s P i x h1 (@lem4449915 A K k z s P i x h2)). Qed.
Lemma lem4449917 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (h1 : term637 A K k z s P i x) : term637 A K k z s P i x.
Proof. exact (fun h0 : term636 A K k z s P i x => @lem4449916 A K k z s P i x h0 h1). Qed.
Lemma lem4449918 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : term639 A K k z s P i x.
Proof. exact (fun h0 : term637 A K k z s P i x => @lem4449917 A K k z s P i x h0). Qed.
Lemma lem4449921 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : term637 A K k z s P i x.
Proof. exact (@lem4449918 A K k z s P i x (@lem4449910 A K k z s P i x)). Qed.
Lemma lem4449922 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : term637 A K k z s P i x.
Proof. exact (@lem4449921 A K k z s P i x). Qed.
Lemma lem4449962 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4449963 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term634 A K k z s P i x) = (term640 A K k z s P i x).
Proof. exact (@lem4449962 (term635 A K k z s P i x)). Qed.
Lemma lem4449965 (t : Prop) : (term45 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4449966 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term640 A K k z s P i x) = (term633 A K k z s P i x).
Proof. exact (@lem4449965 (term633 A K k z s P i x)). Qed.
Lemma lem4449969 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term634 A K k z s P i x) = (term633 A K k z s P i x).
Proof. exact (TRANS (@lem4449963 A K k z s P i x) (@lem4449966 A K k z s P i x)). Qed.
Lemma lem4449986 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term641 A K x s i) = (term641 A K x s i).
Proof. exact (eq_refl (term641 A K x s i)). Qed.
Lemma lem4449987 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term642 A K k z s P i x) = (term643 A K k z s P i x).
Proof. exact (MK_COMB (@lem4449986 A K x s i) (@lem4449969 A K k z s P i x)). Qed.
Lemma lem4449990 {K : Type'} (i : K) (k : K -> Prop) : (term27 K i k) = (term27 K i k).
Proof. exact (eq_refl (term27 K i k)). Qed.
Lemma lem4449991 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term644 A K k z s P i x) = (term645 A K k z s P i x).
Proof. exact (MK_COMB (@lem4449990 K i k) (@lem4449987 A K k z s P i x)). Qed.
Lemma lem4449994 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term545 A K k z s) = (term545 A K k z s).
Proof. exact (eq_refl (term545 A K k z s)). Qed.
Lemma lem4449995 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term646 A K k z s P i x) = (term647 A K k z s P i x).
Proof. exact (MK_COMB (@lem4449994 A K k z s) (@lem4449991 A K k z s P i x)). Qed.
Lemma lem4449998 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term648 A K k s) = (term648 A K k s).
Proof. exact (eq_refl (term648 A K k s)). Qed.
Lemma lem4449999 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term636 A K k z s P i x) = (term649 A K k z s P i x).
Proof. exact (MK_COMB (@lem4449998 A K k s) (@lem4449995 A K k z s P i x)). Qed.
Lemma lem4450002 {A K : Type'} (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term650 A K z s P i x) = (term651 A K z s P i x).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4449999 A K k z s P i x)). Qed.
Lemma lem4450003 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4450004 {A K : Type'} (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term652 A K z s P i x) = (term653 A K z s P i x).
Proof. exact (MK_COMB (@lem4450003 K) (@lem4450002 A K z s P i x)). Qed.
Lemma lem4450009 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term654 A K s P i x) = (term655 A K s P i x).
Proof. exact (fun_ext (fun z : K -> A => @lem4450004 A K z s P i x)). Qed.
Lemma lem4450010 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4450011 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term656 A K s P i x) = (term657 A K s P i x).
Proof. exact (MK_COMB (@lem4450010 A K) (@lem4450009 A K s P i x)). Qed.
Lemma lem4450016 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (term658 A K P i x) = (term659 A K P i x).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4450011 A K s P i x)). Qed.
Lemma lem4450017 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4450018 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (term660 A K P i x) = (term661 A K P i x).
Proof. exact (MK_COMB (@lem4450017 A K) (@lem4450016 A K P i x)). Qed.
Lemma lem4450023 {A K : Type'} (i : K) (x : A) : (term662 A K i x) = (term663 A K i x).
Proof. exact (fun_ext (fun P : type1470 A K => @lem4450018 A K P i x)). Qed.
Lemma lem4450024 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4450025 {A K : Type'} (i : K) (x : A) : (term664 A K i x) = (term665 A K i x).
Proof. exact (MK_COMB (@lem4450024 A K) (@lem4450023 A K i x)). Qed.
Lemma lem4450030 {A K : Type'} (x : A) : (term666 A K x) = (term667 A K x).
Proof. exact (fun_ext (fun i : K => @lem4450025 A K i x)). Qed.
Lemma lem4450031 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4450032 {A K : Type'} (x : A) : (term668 A K x) = (term669 A K x).
Proof. exact (MK_COMB (@lem4450031 K) (@lem4450030 A K x)). Qed.
Lemma lem4450037 {A K : Type'} : (term670 A K) = (term671 A K).
Proof. exact (fun_ext (fun x : A => @lem4450032 A K x)). Qed.
Lemma lem4450038 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4450047 {A K : Type'} : (term672 A K) = (term673 A K).
Proof. exact (MK_COMB (@lem4450038 A) (@lem4450037 A K)). Qed.
Lemma lem4450048 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (P i x) = (P i x).
Proof. exact (eq_refl (P i x)). Qed.
Lemma lem4450049 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (P i x) = (P i x).
Proof. exact (eq_refl (P i x)). Qed.
Lemma lem4450053 {K : Type'} (i' : K) (i : K) (h1 : (i' = i) = False) : (i' = i) = False.
Proof. exact (h1). Qed.
Lemma lem4450054 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4450055 {A K : Type'} (i' : K) (i : K) (h1 : (i' = i) = False) : (term674 A K i' i) = (@COND A False).
Proof. exact (MK_COMB (@lem4450054 A) (@lem4450053 K i' i h1)). Qed.
Lemma lem4450056 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4450057 {A K : Type'} (x : A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term675 A K i' i x) = (@COND A False x).
Proof. exact (MK_COMB (@lem4450055 A K i' i h1) (@lem4450056 A x)). Qed.
Lemma lem4450058 {A K : Type'} (k : K -> Prop) (z : K -> A) (i' : K) : (term627 A K k z i') = (term627 A K k z i').
Proof. exact (eq_refl (term627 A K k z i')). Qed.
Lemma lem4450059 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term590 A K i x k z i') = (term676 A K x k z i').
Proof. exact (MK_COMB (@lem4450057 A K x i' i h1) (@lem4450058 A K k z i')). Qed.
Lemma lem4450061 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4450062 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4450061 A t1 t2). Qed.
Lemma lem4450063 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term676 A K x k z i') = (term627 A K k z i').
Proof. exact (@lem4450062 A x (term627 A K k z i')). Qed.
Lemma lem4450064 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term590 A K i x k z i') = (term627 A K k z i').
Proof. exact (TRANS (@lem4450059 A K x k z i' i h1) (@lem4450063 A K x k z i')). Qed.
Lemma lem4450065 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4450066 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term604 A K i x k z i') = (term677 A K k z i').
Proof. exact (MK_COMB (@lem4450065 A) (@lem4450064 A K x k z i' i h1)). Qed.
Lemma lem4450067 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4450068 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = False) : (term606 A K i x k z s i') = (term678 A K k z s i').
Proof. exact (MK_COMB (@lem4450066 A K x k z i' i h1) (@lem4450067 A K s i')). Qed.
Lemma lem4450069 {K : Type'} (i' : K) (k : K -> Prop) : (term27 K i' k) = (term27 K i' k).
Proof. exact (eq_refl (term27 K i' k)). Qed.
Lemma lem4450070 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = False) : (term608 A K i x k z s i') = (term679 A K k z s i').
Proof. exact (MK_COMB (@lem4450069 K i' k) (@lem4450068 A K x k z s i' i h1)). Qed.
Lemma lem4450073 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : term680 A K i x k z s i'.
Proof. exact (fun h0 : (i' = i) = False => @lem4450070 A K x k z s i' i h0). Qed.
Lemma lem4450075 {K : Type'} (i' : K) (i : K) (h1 : (i' = i) = True) : (i' = i) = True.
Proof. exact (h1). Qed.
Lemma lem4450076 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4450077 {A K : Type'} (i' : K) (i : K) (h1 : (i' = i) = True) : (term674 A K i' i) = (@COND A True).
Proof. exact (MK_COMB (@lem4450076 A) (@lem4450075 K i' i h1)). Qed.
Lemma lem4450078 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4450079 {A K : Type'} (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term675 A K i' i x) = (@COND A True x).
Proof. exact (MK_COMB (@lem4450077 A K i' i h1) (@lem4450078 A x)). Qed.
Lemma lem4450080 {A K : Type'} (k : K -> Prop) (z : K -> A) (i' : K) : (term627 A K k z i') = (term627 A K k z i').
Proof. exact (eq_refl (term627 A K k z i')). Qed.
Lemma lem4450081 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term590 A K i x k z i') = (term681 A K x k z i').
Proof. exact (MK_COMB (@lem4450079 A K x i' i h1) (@lem4450080 A K k z i')). Qed.
Lemma lem4450083 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4450084 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4450083 A t2 t1). Qed.
Lemma lem4450085 {A K : Type'} (k : K -> Prop) (z : K -> A) (i' : K) (x : A) : (term681 A K x k z i') = x.
Proof. exact (@lem4450084 A (term627 A K k z i') x). Qed.
Lemma lem4450086 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term590 A K i x k z i') = x.
Proof. exact (TRANS (@lem4450081 A K x k z i' i h1) (@lem4450085 A K k z i' x)). Qed.
Lemma lem4450087 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4450088 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term604 A K i x k z i') = (@IN A x).
Proof. exact (MK_COMB (@lem4450087 A) (@lem4450086 A K k z x i' i h1)). Qed.
Lemma lem4450089 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4450090 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (s : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = True) : (term606 A K i x k z s i') = (term15 A K x s i').
Proof. exact (MK_COMB (@lem4450088 A K k z x i' i h1) (@lem4450089 A K s i')). Qed.
Lemma lem4450091 {K : Type'} (i' : K) (k : K -> Prop) : (term27 K i' k) = (term27 K i' k).
Proof. exact (eq_refl (term27 K i' k)). Qed.
Lemma lem4450092 {A K : Type'} (z : K -> A) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = True) : (term608 A K i x k z s i') = (term29 A K k x s i').
Proof. exact (MK_COMB (@lem4450091 K i' k) (@lem4450090 A K k z x s i' i h1)). Qed.
Lemma lem4450095 {A K : Type'} (i : K) (z : K -> A) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : term682 A K i z k x s i'.
Proof. exact (fun h0 : (i' = i) = True => @lem4450092 A K z k x s i' i h0). Qed.
Lemma lem4450096 {A K : Type'} (i : K) (z : K -> A) (k : K -> Prop) (x : A) (s : type1470 A K) (i' : K) : term683 A K i z k x s i'.
Proof. exact (conj (@lem4450073 A K i x k z s i') (@lem4450095 A K i z k x s i')). Qed.
Lemma lem4450098 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term684 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4450099 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : term685 A K x i k z s i'.
Proof. exact (@lem4450098 (term608 A K i x k z s i') (term29 A K k x s i') (i' = i) (term679 A K k z s i')). Qed.
Lemma lem4450114 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term608 A K i x k z s i') = (term686 A K x i k z s i').
Proof. exact (@lem4450099 A K x i k z s i' (@lem4450096 A K i z k x s i')). Qed.
Lemma lem4450120 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (@IN K i' k) = False.
Proof. exact (h1). Qed.
Lemma lem4450121 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4450122 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term27 K i' k) = (imp False).
Proof. exact (MK_COMB (@lem4450121) (@lem4450120 K i' k h1)). Qed.
Lemma lem4450123 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term15 A K x s i') = (term15 A K x s i').
Proof. exact (eq_refl (term15 A K x s i')). Qed.
Lemma lem4450124 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term29 A K k x s i') = (term687 A K x s i').
Proof. exact (MK_COMB (@lem4450122 K i' k h1) (@lem4450123 A K x s i')). Qed.
Lemma lem4450126 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4450127 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term687 A K x s i') = True.
Proof. exact (@lem4450126 (term15 A K x s i')). Qed.
Lemma lem4450128 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term29 A K k x s i') = True.
Proof. exact (TRANS (@lem4450124 A K x s i' k h1) (@lem4450127 A K x s i')). Qed.
Lemma lem4450129 {K : Type'} (i' : K) (i : K) : (term688 K i' i) = (term688 K i' i).
Proof. exact (eq_refl (term688 K i' i)). Qed.
Lemma lem4450130 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term689 A K i k x s i') = (term690 K i' i).
Proof. exact (MK_COMB (@lem4450129 K i' i) (@lem4450128 A K x s i' k h1)). Qed.
Lemma lem4450132 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4450133 {K : Type'} (i' : K) (i : K) : (term690 K i' i) = True.
Proof. exact (@lem4450132 (term691 K i' i)). Qed.
Lemma lem4450134 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term689 A K i k x s i') = True.
Proof. exact (TRANS (@lem4450130 A K x s i i' k h1) (@lem4450133 K i' i)). Qed.
Lemma lem4450135 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4450136 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term692 A K i k x s i') = (and True).
Proof. exact (MK_COMB (@lem4450135) (@lem4450134 A K i x s i' k h1)). Qed.
Lemma lem4450140 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (@IN K i' k) = False.
Proof. exact (h1). Qed.
Lemma lem4450141 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4450142 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term27 K i' k) = (imp False).
Proof. exact (MK_COMB (@lem4450141) (@lem4450140 K i' k h1)). Qed.
Lemma lem4450144 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (@IN K i' k) = False.
Proof. exact (h1). Qed.
Lemma lem4450145 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4450146 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term693 A K i' k) = (@COND A False).
Proof. exact (MK_COMB (@lem4450145 A) (@lem4450144 K i' k h1)). Qed.
Lemma lem4450147 {A K : Type'} (z : K -> A) (i' : K) : (z i') = (z i').
Proof. exact (eq_refl (z i')). Qed.
Lemma lem4450148 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term694 A K k z i') = (term695 A K z i').
Proof. exact (MK_COMB (@lem4450146 A K i' k h1) (@lem4450147 A K z i')). Qed.
Lemma lem4450149 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4450150 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term627 A K k z i') = (term696 A K z i').
Proof. exact (MK_COMB (@lem4450148 A K z i' k h1) (@lem4450149 A)). Qed.
Lemma lem4450152 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4450153 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4450152 A t1 t2). Qed.
Lemma lem4450154 {A K : Type'} (z : K -> A) (i' : K) : (term696 A K z i') = (@ARB A).
Proof. exact (@lem4450153 A (z i') (@ARB A)). Qed.
Lemma lem4450155 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term627 A K k z i') = (@ARB A).
Proof. exact (TRANS (@lem4450150 A K z i' k h1) (@lem4450154 A K z i')). Qed.
Lemma lem4450156 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4450157 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term677 A K k z i') = (@IN A (@ARB A)).
Proof. exact (MK_COMB (@lem4450156 A) (@lem4450155 A K z i' k h1)). Qed.
Lemma lem4450158 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4450159 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term678 A K k z s i') = (term697 A K s i').
Proof. exact (MK_COMB (@lem4450157 A K z i' k h1) (@lem4450158 A K s i')). Qed.
Lemma lem4450160 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term679 A K k z s i') = (term698 A K s i').
Proof. exact (MK_COMB (@lem4450142 K i' k h1) (@lem4450159 A K z s i' k h1)). Qed.
Lemma lem4450162 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4450163 {A K : Type'} (s : type1470 A K) (i' : K) : (term698 A K s i') = True.
Proof. exact (@lem4450162 (term697 A K s i')). Qed.
Lemma lem4450164 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term679 A K k z s i') = True.
Proof. exact (TRANS (@lem4450160 A K z s i' k h1) (@lem4450163 A K s i')). Qed.
Lemma lem4450165 {K : Type'} (i' : K) (i : K) : (term699 K i' i) = (term699 K i' i).
Proof. exact (eq_refl (term699 K i' i)). Qed.
Lemma lem4450166 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term700 A K i k z s i') = (term701 K i' i).
Proof. exact (MK_COMB (@lem4450165 K i' i) (@lem4450164 A K z s i' k h1)). Qed.
Lemma lem4450168 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4450169 {K : Type'} (i' : K) (i : K) : (term701 K i' i) = True.
Proof. exact (@lem4450168 (i' = i)). Qed.
Lemma lem4450170 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term700 A K i k z s i') = True.
Proof. exact (TRANS (@lem4450166 A K z s i i' k h1) (@lem4450169 K i' i)). Qed.
Lemma lem4450171 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term686 A K x i k z s i') = (True /\ True).
Proof. exact (MK_COMB (@lem4450136 A K i x s i' k h1) (@lem4450170 A K i z s i' k h1)). Qed.
Lemma lem4450173 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4450174 : (True /\ True) = True.
Proof. exact (@lem4450173 True). Qed.
Lemma lem4450175 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term686 A K x i k z s i') = True.
Proof. exact (TRANS (@lem4450171 A K x i z s i' k h1) (@lem4450174)). Qed.
Lemma lem4450176 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : term702 A K x i k z s i'.
Proof. exact (fun h0 : (@IN K i' k) = False => @lem4450175 A K x i z s i' k h0). Qed.
Lemma lem4450180 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (@IN K i' k) = True.
Proof. exact (h1). Qed.
Lemma lem4450181 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4450182 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term27 K i' k) = (imp True).
Proof. exact (MK_COMB (@lem4450181) (@lem4450180 K i' k h1)). Qed.
Lemma lem4450183 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term15 A K x s i') = (term15 A K x s i').
Proof. exact (eq_refl (term15 A K x s i')). Qed.
Lemma lem4450184 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term29 A K k x s i') = (term703 A K x s i').
Proof. exact (MK_COMB (@lem4450182 K i' k h1) (@lem4450183 A K x s i')). Qed.
Lemma lem4450186 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4450187 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term703 A K x s i') = (term15 A K x s i').
Proof. exact (@lem4450186 (term15 A K x s i')). Qed.
Lemma lem4450188 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term29 A K k x s i') = (term15 A K x s i').
Proof. exact (TRANS (@lem4450184 A K x s i' k h1) (@lem4450187 A K x s i')). Qed.
Lemma lem4450189 {K : Type'} (i' : K) (i : K) : (term688 K i' i) = (term688 K i' i).
Proof. exact (eq_refl (term688 K i' i)). Qed.
Lemma lem4450190 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term689 A K i k x s i') = (term704 A K i x s i').
Proof. exact (MK_COMB (@lem4450189 K i' i) (@lem4450188 A K x s i' k h1)). Qed.
Lemma lem4450193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4450194 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term692 A K i k x s i') = (term705 A K i x s i').
Proof. exact (MK_COMB (@lem4450193) (@lem4450190 A K i x s i' k h1)). Qed.
Lemma lem4450198 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (@IN K i' k) = True.
Proof. exact (h1). Qed.
Lemma lem4450199 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4450200 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term27 K i' k) = (imp True).
Proof. exact (MK_COMB (@lem4450199) (@lem4450198 K i' k h1)). Qed.
Lemma lem4450202 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (@IN K i' k) = True.
Proof. exact (h1). Qed.
Lemma lem4450203 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4450204 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term693 A K i' k) = (@COND A True).
Proof. exact (MK_COMB (@lem4450203 A) (@lem4450202 K i' k h1)). Qed.
Lemma lem4450205 {A K : Type'} (z : K -> A) (i' : K) : (z i') = (z i').
Proof. exact (eq_refl (z i')). Qed.
Lemma lem4450206 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term694 A K k z i') = (term706 A K z i').
Proof. exact (MK_COMB (@lem4450204 A K i' k h1) (@lem4450205 A K z i')). Qed.
Lemma lem4450207 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4450208 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term627 A K k z i') = (term707 A K z i').
Proof. exact (MK_COMB (@lem4450206 A K z i' k h1) (@lem4450207 A)). Qed.
Lemma lem4450210 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4450211 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4450210 A t2 t1). Qed.
Lemma lem4450212 {A K : Type'} (z : K -> A) (i' : K) : (term707 A K z i') = (z i').
Proof. exact (@lem4450211 A (@ARB A) (z i')). Qed.
Lemma lem4450213 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term627 A K k z i') = (z i').
Proof. exact (TRANS (@lem4450208 A K z i' k h1) (@lem4450212 A K z i')). Qed.
Lemma lem4450214 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4450215 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term677 A K k z i') = (term457 A K z i').
Proof. exact (MK_COMB (@lem4450214 A) (@lem4450213 A K z i' k h1)). Qed.
Lemma lem4450216 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4450217 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term678 A K k z s i') = (term451 A K z s i').
Proof. exact (MK_COMB (@lem4450215 A K z i' k h1) (@lem4450216 A K s i')). Qed.
Lemma lem4450218 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term679 A K k z s i') = (term708 A K z s i').
Proof. exact (MK_COMB (@lem4450200 K i' k h1) (@lem4450217 A K z s i' k h1)). Qed.
Lemma lem4450220 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4450221 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) : (term708 A K z s i') = (term451 A K z s i').
Proof. exact (@lem4450220 (term451 A K z s i')). Qed.
Lemma lem4450222 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term679 A K k z s i') = (term451 A K z s i').
Proof. exact (TRANS (@lem4450218 A K z s i' k h1) (@lem4450221 A K z s i')). Qed.
Lemma lem4450223 {K : Type'} (i' : K) (i : K) : (term699 K i' i) = (term699 K i' i).
Proof. exact (eq_refl (term699 K i' i)). Qed.
Lemma lem4450224 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term700 A K i k z s i') = (term709 A K i z s i').
Proof. exact (MK_COMB (@lem4450223 K i' i) (@lem4450222 A K z s i' k h1)). Qed.
Lemma lem4450227 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term686 A K x i k z s i') = (term710 A K x i z s i').
Proof. exact (MK_COMB (@lem4450194 A K i x s i' k h1) (@lem4450224 A K i z s i' k h1)). Qed.
Lemma lem4450230 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : term711 A K k x i z s i'.
Proof. exact (fun h0 : (@IN K i' k) = True => @lem4450227 A K x i z s i' k h0). Qed.
Lemma lem4450231 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : term712 A K k x i z s i'.
Proof. exact (conj (@lem4450176 A K x i k z s i') (@lem4450230 A K k x i z s i')). Qed.
Lemma lem4450233 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term684 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4450234 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) : term713 A K x i z s i' k.
Proof. exact (@lem4450233 (term686 A K x i k z s i') (term710 A K x i z s i') (@IN K i' k) True). Qed.
Lemma lem4450235 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) : (term686 A K x i k z s i') = (term714 A K x i z s i' k).
Proof. exact (@lem4450234 A K x i z s i' k (@lem4450231 A K k x i z s i')). Qed.
Lemma lem4450237 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4450238 {K : Type'} (i' : K) (k : K -> Prop) : (term715 K i' k) = True.
Proof. exact (@lem4450237 (@IN K i' k)). Qed.
Lemma lem4450243 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term716 A K k x i z s i') = (term716 A K k x i z s i').
Proof. exact (eq_refl (term716 A K k x i z s i')). Qed.
Lemma lem4450244 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term714 A K x i z s i' k) = (term717 A K k x i z s i').
Proof. exact (MK_COMB (@lem4450243 A K k x i z s i') (@lem4450238 K i' k)). Qed.
Lemma lem4450246 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4450247 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term717 A K k x i z s i') = (term718 A K k x i z s i').
Proof. exact (@lem4450246 (term718 A K k x i z s i')). Qed.
Lemma lem4450248 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term714 A K x i z s i' k) = (term718 A K k x i z s i').
Proof. exact (TRANS (@lem4450244 A K k x i z s i') (@lem4450247 A K k x i z s i')). Qed.
Lemma lem4450273 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term686 A K x i k z s i') = (term718 A K k x i z s i').
Proof. exact (TRANS (@lem4450235 A K x i z s i' k) (@lem4450248 A K k x i z s i')). Qed.
Lemma lem4450274 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) : (term719 A K i x k z s i') = (term719 A K i x k z s i').
Proof. exact (eq_refl (term719 A K i x k z s i')). Qed.
Lemma lem4450275 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : ((term608 A K i x k z s i') = (term686 A K x i k z s i')) = ((term608 A K i x k z s i') = (term718 A K k x i z s i')).
Proof. exact (MK_COMB (@lem4450274 A K i x k z s i') (@lem4450273 A K k x i z s i')). Qed.
Lemma lem4450276 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term608 A K i x k z s i') = (term718 A K k x i z s i').
Proof. exact (EQ_MP (@lem4450275 A K k x i z s i') (@lem4450114 A K x i k z s i')). Qed.
Lemma lem4450277 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term610 A K i x k z s) = (term720 A K k x i z s).
Proof. exact (fun_ext (fun i' : K => @lem4450276 A K k x i z s i')). Qed.
Lemma lem4450278 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4450279 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term612 A K i x k z s) = (term721 A K k x i z s).
Proof. exact (MK_COMB (@lem4450278 K) (@lem4450277 A K k x i z s)). Qed.
Lemma lem4450283 {K : Type'} (x : K) (i : K) (h1 : (x = i) = False) : (x = i) = False.
Proof. exact (h1). Qed.
Lemma lem4450284 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4450285 {A K : Type'} (x : K) (i : K) (h1 : (x = i) = False) : (term674 A K x i) = (@COND A False).
Proof. exact (MK_COMB (@lem4450284 A) (@lem4450283 K x i h1)). Qed.
Lemma lem4450286 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4450287 {A K : Type'} (x : A) (x' : K) (i : K) (h1 : (x' = i) = False) : (term675 A K x' i x) = (@COND A False x).
Proof. exact (MK_COMB (@lem4450285 A K x' i h1) (@lem4450286 A x)). Qed.
Lemma lem4450288 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : K) : (term627 A K k z x) = (term627 A K k z x).
Proof. exact (eq_refl (term627 A K k z x)). Qed.
Lemma lem4450289 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (x' : K) (i : K) (h1 : (x' = i) = False) : (term590 A K i x k z x') = (term676 A K x k z x').
Proof. exact (MK_COMB (@lem4450287 A K x x' i h1) (@lem4450288 A K k z x')). Qed.
Lemma lem4450291 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4450292 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4450291 A t1 t2). Qed.
Lemma lem4450293 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (x' : K) : (term676 A K x k z x') = (term627 A K k z x').
Proof. exact (@lem4450292 A x (term627 A K k z x')). Qed.
Lemma lem4450294 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (x' : K) (i : K) (h1 : (x' = i) = False) : (term590 A K i x k z x') = (term627 A K k z x').
Proof. exact (TRANS (@lem4450289 A K x k z x' i h1) (@lem4450293 A K x k z x')). Qed.
Lemma lem4450295 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4450296 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (x' : K) (i : K) (h1 : (x' = i) = False) : (term594 A K i x k z x') = (term722 A K k z x').
Proof. exact (MK_COMB (@lem4450295 A) (@lem4450294 A K x k z x' i h1)). Qed.
Lemma lem4450297 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4450298 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (x' : K) (i : K) (h1 : (x' = i) = False) : ((term590 A K i x k z x') = (@ARB A)) = ((term627 A K k z x') = (@ARB A)).
Proof. exact (MK_COMB (@lem4450296 A K x k z x' i h1) (@lem4450297 A)). Qed.
Lemma lem4450301 {K : Type'} (x : K) (k : K -> Prop) : (term595 K x k) = (term595 K x k).
Proof. exact (eq_refl (term595 K x k)). Qed.
Lemma lem4450302 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (x' : K) (i : K) (h1 : (x' = i) = False) : (term597 A K i x k z x') = (term723 A K k z x').
Proof. exact (MK_COMB (@lem4450301 K x' k) (@lem4450298 A K x k z x' i h1)). Qed.
Lemma lem4450305 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (x' : K) : term724 A K i x k z x'.
Proof. exact (fun h0 : (x' = i) = False => @lem4450302 A K x k z x' i h0). Qed.
Lemma lem4450307 {K : Type'} (x : K) (i : K) (h1 : (x = i) = True) : (x = i) = True.
Proof. exact (h1). Qed.
Lemma lem4450308 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4450309 {A K : Type'} (x : K) (i : K) (h1 : (x = i) = True) : (term674 A K x i) = (@COND A True).
Proof. exact (MK_COMB (@lem4450308 A) (@lem4450307 K x i h1)). Qed.
Lemma lem4450310 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4450311 {A K : Type'} (x : A) (x' : K) (i : K) (h1 : (x' = i) = True) : (term675 A K x' i x) = (@COND A True x).
Proof. exact (MK_COMB (@lem4450309 A K x' i h1) (@lem4450310 A x)). Qed.
Lemma lem4450312 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : K) : (term627 A K k z x) = (term627 A K k z x).
Proof. exact (eq_refl (term627 A K k z x)). Qed.
Lemma lem4450313 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (x' : K) (i : K) (h1 : (x' = i) = True) : (term590 A K i x k z x') = (term681 A K x k z x').
Proof. exact (MK_COMB (@lem4450311 A K x x' i h1) (@lem4450312 A K k z x')). Qed.
Lemma lem4450315 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4450316 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4450315 A t2 t1). Qed.
Lemma lem4450317 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : K) (x' : A) : (term681 A K x' k z x) = x'.
Proof. exact (@lem4450316 A (term627 A K k z x) x'). Qed.
Lemma lem4450318 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (x' : K) (i : K) (h1 : (x' = i) = True) : (term590 A K i x k z x') = x.
Proof. exact (TRANS (@lem4450313 A K x k z x' i h1) (@lem4450317 A K k z x' x)). Qed.
Lemma lem4450319 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4450320 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (x' : K) (i : K) (h1 : (x' = i) = True) : (term594 A K i x k z x') = (@eq A x).
Proof. exact (MK_COMB (@lem4450319 A) (@lem4450318 A K k z x x' i h1)). Qed.
Lemma lem4450321 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4450322 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (x' : K) (i : K) (h1 : (x' = i) = True) : ((term590 A K i x k z x') = (@ARB A)) = (x = (@ARB A)).
Proof. exact (MK_COMB (@lem4450320 A K k z x x' i h1) (@lem4450321 A)). Qed.
Lemma lem4450325 {K : Type'} (x : K) (k : K -> Prop) : (term595 K x k) = (term595 K x k).
Proof. exact (eq_refl (term595 K x k)). Qed.
Lemma lem4450326 {A K : Type'} (z : K -> A) (k : K -> Prop) (x : A) (x' : K) (i : K) (h1 : (x' = i) = True) : (term597 A K i x k z x') = (term725 A K x' k x).
Proof. exact (MK_COMB (@lem4450325 K x' k) (@lem4450322 A K k z x x' i h1)). Qed.
Lemma lem4450329 {A K : Type'} (i : K) (z : K -> A) (x : K) (k : K -> Prop) (x' : A) : term726 A K i z x k x'.
Proof. exact (fun h0 : (x = i) = True => @lem4450326 A K z k x' x i h0). Qed.
Lemma lem4450330 {A K : Type'} (i : K) (z : K -> A) (x : K) (k : K -> Prop) (x' : A) : term727 A K i z x k x'.
Proof. exact (conj (@lem4450305 A K i x' k z x) (@lem4450329 A K i z x k x')). Qed.
Lemma lem4450332 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term684 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4450333 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (x' : K) : term728 A K x i k z x'.
Proof. exact (@lem4450332 (term597 A K i x k z x') (term725 A K x' k x) (x' = i) (term723 A K k z x')). Qed.
Lemma lem4450348 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (x' : K) : (term597 A K i x k z x') = (term729 A K x i k z x').
Proof. exact (@lem4450333 A K x i k z x' (@lem4450330 A K i z x' k x)). Qed.
Lemma lem4450354 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (@IN K x k) = False.
Proof. exact (h1). Qed.
Lemma lem4450355 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4450356 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term473 K x k) = (~ False).
Proof. exact (MK_COMB (@lem4450355) (@lem4450354 K x k h1)). Qed.
Lemma lem4450358 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4450359 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term473 K x k) = True.
Proof. exact (TRANS (@lem4450356 K x k h1) (@lem4450358)). Qed.
Lemma lem4450360 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4450361 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term595 K x k) = (imp True).
Proof. exact (MK_COMB (@lem4450360) (@lem4450359 K x k h1)). Qed.
Lemma lem4450364 {A : Type'} (x : A) : (x = (@ARB A)) = (x = (@ARB A)).
Proof. exact (eq_refl (x = (@ARB A))). Qed.
Lemma lem4450365 {A K : Type'} (x : A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = False) : (term725 A K x' k x) = (term730 A x).
Proof. exact (MK_COMB (@lem4450361 K x' k h1) (@lem4450364 A x)). Qed.
Lemma lem4450367 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4450368 {A : Type'} (x : A) : (term730 A x) = (x = (@ARB A)).
Proof. exact (@lem4450367 (x = (@ARB A))). Qed.
Lemma lem4450371 {A K : Type'} (x : A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = False) : (term725 A K x' k x) = (x = (@ARB A)).
Proof. exact (TRANS (@lem4450365 A K x x' k h1) (@lem4450368 A x)). Qed.
Lemma lem4450372 {K : Type'} (x : K) (i : K) : (term688 K x i) = (term688 K x i).
Proof. exact (eq_refl (term688 K x i)). Qed.
Lemma lem4450373 {A K : Type'} (i : K) (x : A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = False) : (term731 A K i x' k x) = (term732 A K x' i x).
Proof. exact (MK_COMB (@lem4450372 K x' i) (@lem4450371 A K x x' k h1)). Qed.
Lemma lem4450376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4450377 {A K : Type'} (i : K) (x : A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = False) : (term733 A K i x' k x) = (term734 A K x' i x).
Proof. exact (MK_COMB (@lem4450376) (@lem4450373 A K i x x' k h1)). Qed.
Lemma lem4450381 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (@IN K x k) = False.
Proof. exact (h1). Qed.
Lemma lem4450382 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4450383 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term473 K x k) = (~ False).
Proof. exact (MK_COMB (@lem4450382) (@lem4450381 K x k h1)). Qed.
Lemma lem4450385 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4450386 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term473 K x k) = True.
Proof. exact (TRANS (@lem4450383 K x k h1) (@lem4450385)). Qed.
Lemma lem4450387 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4450388 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term595 K x k) = (imp True).
Proof. exact (MK_COMB (@lem4450387) (@lem4450386 K x k h1)). Qed.
Lemma lem4450390 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (@IN K x k) = False.
Proof. exact (h1). Qed.
Lemma lem4450391 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4450392 {A K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term693 A K x k) = (@COND A False).
Proof. exact (MK_COMB (@lem4450391 A) (@lem4450390 K x k h1)). Qed.
Lemma lem4450393 {A K : Type'} (z : K -> A) (x : K) : (z x) = (z x).
Proof. exact (eq_refl (z x)). Qed.
Lemma lem4450394 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term694 A K k z x) = (term695 A K z x).
Proof. exact (MK_COMB (@lem4450392 A K x k h1) (@lem4450393 A K z x)). Qed.
Lemma lem4450395 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4450396 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term627 A K k z x) = (term696 A K z x).
Proof. exact (MK_COMB (@lem4450394 A K z x k h1) (@lem4450395 A)). Qed.
Lemma lem4450398 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4450399 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4450398 A t1 t2). Qed.
Lemma lem4450400 {A K : Type'} (z : K -> A) (x : K) : (term696 A K z x) = (@ARB A).
Proof. exact (@lem4450399 A (z x) (@ARB A)). Qed.
Lemma lem4450401 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term627 A K k z x) = (@ARB A).
Proof. exact (TRANS (@lem4450396 A K z x k h1) (@lem4450400 A K z x)). Qed.
Lemma lem4450402 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4450403 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term722 A K k z x) = (@eq A (@ARB A)).
Proof. exact (MK_COMB (@lem4450402 A) (@lem4450401 A K z x k h1)). Qed.
Lemma lem4450404 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4450405 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : ((term627 A K k z x) = (@ARB A)) = ((@ARB A) = (@ARB A)).
Proof. exact (MK_COMB (@lem4450403 A K z x k h1) (@lem4450404 A)). Qed.
Lemma lem4450407 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4450408 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem4450407 A x). Qed.
Lemma lem4450409 {A : Type'} : ((@ARB A) = (@ARB A)) = True.
Proof. exact (@lem4450408 A (@ARB A)). Qed.
Lemma lem4450410 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : ((term627 A K k z x) = (@ARB A)) = True.
Proof. exact (TRANS (@lem4450405 A K z x k h1) (@lem4450409 A)). Qed.
Lemma lem4450411 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term723 A K k z x) = (True -> True).
Proof. exact (MK_COMB (@lem4450388 K x k h1) (@lem4450410 A K z x k h1)). Qed.
Lemma lem4450413 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4450414 : (True -> True) = True.
Proof. exact (@lem4450413 True). Qed.
Lemma lem4450415 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term723 A K k z x) = True.
Proof. exact (TRANS (@lem4450411 A K z x k h1) (@lem4450414)). Qed.
Lemma lem4450416 {K : Type'} (x : K) (i : K) : (term699 K x i) = (term699 K x i).
Proof. exact (eq_refl (term699 K x i)). Qed.
Lemma lem4450417 {A K : Type'} (z : K -> A) (i : K) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term735 A K i k z x) = (term701 K x i).
Proof. exact (MK_COMB (@lem4450416 K x i) (@lem4450415 A K z x k h1)). Qed.
Lemma lem4450419 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4450420 {K : Type'} (x : K) (i : K) : (term701 K x i) = True.
Proof. exact (@lem4450419 (x = i)). Qed.
Lemma lem4450421 {A K : Type'} (i : K) (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term735 A K i k z x) = True.
Proof. exact (TRANS (@lem4450417 A K z i x k h1) (@lem4450420 K x i)). Qed.
Lemma lem4450422 {A K : Type'} (z : K -> A) (i : K) (x : A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = False) : (term729 A K x i k z x') = (term736 A K x' i x).
Proof. exact (MK_COMB (@lem4450377 A K i x x' k h1) (@lem4450421 A K i z x' k h1)). Qed.
Lemma lem4450424 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4450425 {A K : Type'} (x : K) (i : K) (x' : A) : (term736 A K x i x') = (term732 A K x i x').
Proof. exact (@lem4450424 (term732 A K x i x')). Qed.
Lemma lem4450428 {A K : Type'} (z : K -> A) (i : K) (x : A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = False) : (term729 A K x i k z x') = (term732 A K x' i x).
Proof. exact (TRANS (@lem4450422 A K z i x x' k h1) (@lem4450425 A K x' i x)). Qed.
Lemma lem4450429 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : K) (i : K) (x' : A) : term737 A K k z x i x'.
Proof. exact (fun h0 : (@IN K x k) = False => @lem4450428 A K z i x' x k h0). Qed.
Lemma lem4450433 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (@IN K x k) = True.
Proof. exact (h1). Qed.
Lemma lem4450434 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4450435 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term473 K x k) = (~ True).
Proof. exact (MK_COMB (@lem4450434) (@lem4450433 K x k h1)). Qed.
Lemma lem4450437 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4450438 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term473 K x k) = False.
Proof. exact (TRANS (@lem4450435 K x k h1) (@lem4450437)). Qed.
Lemma lem4450439 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4450440 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term595 K x k) = (imp False).
Proof. exact (MK_COMB (@lem4450439) (@lem4450438 K x k h1)). Qed.
Lemma lem4450443 {A : Type'} (x : A) : (x = (@ARB A)) = (x = (@ARB A)).
Proof. exact (eq_refl (x = (@ARB A))). Qed.
Lemma lem4450444 {A K : Type'} (x : A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = True) : (term725 A K x' k x) = (term738 A x).
Proof. exact (MK_COMB (@lem4450440 K x' k h1) (@lem4450443 A x)). Qed.
Lemma lem4450446 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4450447 {A : Type'} (x : A) : (term738 A x) = True.
Proof. exact (@lem4450446 (x = (@ARB A))). Qed.
Lemma lem4450448 {A K : Type'} (x : A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = True) : (term725 A K x' k x) = True.
Proof. exact (TRANS (@lem4450444 A K x x' k h1) (@lem4450447 A x)). Qed.
Lemma lem4450449 {K : Type'} (x : K) (i : K) : (term688 K x i) = (term688 K x i).
Proof. exact (eq_refl (term688 K x i)). Qed.
Lemma lem4450450 {A K : Type'} (x : A) (i : K) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = True) : (term731 A K i x' k x) = (term690 K x' i).
Proof. exact (MK_COMB (@lem4450449 K x' i) (@lem4450448 A K x x' k h1)). Qed.
Lemma lem4450452 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4450453 {K : Type'} (x : K) (i : K) : (term690 K x i) = True.
Proof. exact (@lem4450452 (term691 K x i)). Qed.
Lemma lem4450454 {A K : Type'} (i : K) (x : A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = True) : (term731 A K i x' k x) = True.
Proof. exact (TRANS (@lem4450450 A K x i x' k h1) (@lem4450453 K x' i)). Qed.
Lemma lem4450455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4450456 {A K : Type'} (i : K) (x : A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = True) : (term733 A K i x' k x) = (and True).
Proof. exact (MK_COMB (@lem4450455) (@lem4450454 A K i x x' k h1)). Qed.
Lemma lem4450460 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (@IN K x k) = True.
Proof. exact (h1). Qed.
Lemma lem4450461 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4450462 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term473 K x k) = (~ True).
Proof. exact (MK_COMB (@lem4450461) (@lem4450460 K x k h1)). Qed.
Lemma lem4450464 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4450465 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term473 K x k) = False.
Proof. exact (TRANS (@lem4450462 K x k h1) (@lem4450464)). Qed.
Lemma lem4450466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4450467 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term595 K x k) = (imp False).
Proof. exact (MK_COMB (@lem4450466) (@lem4450465 K x k h1)). Qed.
Lemma lem4450469 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (@IN K x k) = True.
Proof. exact (h1). Qed.
Lemma lem4450470 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4450471 {A K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term693 A K x k) = (@COND A True).
Proof. exact (MK_COMB (@lem4450470 A) (@lem4450469 K x k h1)). Qed.
Lemma lem4450472 {A K : Type'} (z : K -> A) (x : K) : (z x) = (z x).
Proof. exact (eq_refl (z x)). Qed.
Lemma lem4450473 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term694 A K k z x) = (term706 A K z x).
Proof. exact (MK_COMB (@lem4450471 A K x k h1) (@lem4450472 A K z x)). Qed.
Lemma lem4450474 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4450475 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term627 A K k z x) = (term707 A K z x).
Proof. exact (MK_COMB (@lem4450473 A K z x k h1) (@lem4450474 A)). Qed.
Lemma lem4450477 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4450478 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4450477 A t2 t1). Qed.
Lemma lem4450479 {A K : Type'} (z : K -> A) (x : K) : (term707 A K z x) = (z x).
Proof. exact (@lem4450478 A (@ARB A) (z x)). Qed.
Lemma lem4450480 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term627 A K k z x) = (z x).
Proof. exact (TRANS (@lem4450475 A K z x k h1) (@lem4450479 A K z x)). Qed.
Lemma lem4450481 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4450482 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term722 A K k z x) = (term739 A K z x).
Proof. exact (MK_COMB (@lem4450481 A) (@lem4450480 A K z x k h1)). Qed.
Lemma lem4450483 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4450484 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : ((term627 A K k z x) = (@ARB A)) = ((z x) = (@ARB A)).
Proof. exact (MK_COMB (@lem4450482 A K z x k h1) (@lem4450483 A)). Qed.
Lemma lem4450487 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term723 A K k z x) = (term740 A K z x).
Proof. exact (MK_COMB (@lem4450467 K x k h1) (@lem4450484 A K z x k h1)). Qed.
Lemma lem4450489 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4450490 {A K : Type'} (z : K -> A) (x : K) : (term740 A K z x) = True.
Proof. exact (@lem4450489 ((z x) = (@ARB A))). Qed.
Lemma lem4450491 {A K : Type'} (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term723 A K k z x) = True.
Proof. exact (TRANS (@lem4450487 A K z x k h1) (@lem4450490 A K z x)). Qed.
Lemma lem4450492 {K : Type'} (x : K) (i : K) : (term699 K x i) = (term699 K x i).
Proof. exact (eq_refl (term699 K x i)). Qed.
Lemma lem4450493 {A K : Type'} (z : K -> A) (i : K) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term735 A K i k z x) = (term701 K x i).
Proof. exact (MK_COMB (@lem4450492 K x i) (@lem4450491 A K z x k h1)). Qed.
Lemma lem4450495 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4450496 {K : Type'} (x : K) (i : K) : (term701 K x i) = True.
Proof. exact (@lem4450495 (x = i)). Qed.
Lemma lem4450497 {A K : Type'} (i : K) (z : K -> A) (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term735 A K i k z x) = True.
Proof. exact (TRANS (@lem4450493 A K z i x k h1) (@lem4450496 K x i)). Qed.
Lemma lem4450498 {A K : Type'} (x : A) (i : K) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = True) : (term729 A K x i k z x') = (True /\ True).
Proof. exact (MK_COMB (@lem4450456 A K i x x' k h1) (@lem4450497 A K i z x' k h1)). Qed.
Lemma lem4450500 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4450501 : (True /\ True) = True.
Proof. exact (@lem4450500 True). Qed.
Lemma lem4450502 {A K : Type'} (x : A) (i : K) (z : K -> A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = True) : (term729 A K x i k z x') = True.
Proof. exact (TRANS (@lem4450498 A K x i z x' k h1) (@lem4450501)). Qed.
Lemma lem4450503 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (x' : K) : term741 A K x i k z x'.
Proof. exact (fun h0 : (@IN K x' k) = True => @lem4450502 A K x i z x' k h0). Qed.
Lemma lem4450504 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (z : K -> A) (x' : K) : term742 A K x i k z x'.
Proof. exact (conj (@lem4450429 A K k z x' i x) (@lem4450503 A K x i k z x')). Qed.
Lemma lem4450506 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term684 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4450507 {A K : Type'} (z : K -> A) (k : K -> Prop) (x : K) (i : K) (x' : A) : term743 A K z k x i x'.
Proof. exact (@lem4450506 (term729 A K x' i k z x) True (@IN K x k) (term732 A K x i x')). Qed.
Lemma lem4450508 {A K : Type'} (z : K -> A) (k : K -> Prop) (x : K) (i : K) (x' : A) : (term729 A K x' i k z x) = (term744 A K k x i x').
Proof. exact (@lem4450507 A K z k x i x' (@lem4450504 A K x' i k z x)). Qed.
Lemma lem4450511 {A K : Type'} (k : K -> Prop) (x : K) (i : K) (x' : A) : (term745 A K k x i x') = (term745 A K k x i x').
Proof. exact (eq_refl (term745 A K k x i x')). Qed.
Lemma lem4450513 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4450514 {K : Type'} (x : K) (k : K -> Prop) : (term746 K x k) = True.
Proof. exact (@lem4450513 (term473 K x k)). Qed.
Lemma lem4450515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4450516 {K : Type'} (x : K) (k : K -> Prop) : (term747 K x k) = (and True).
Proof. exact (MK_COMB (@lem4450515) (@lem4450514 K x k)). Qed.
Lemma lem4450517 {A K : Type'} (k : K -> Prop) (x : K) (i : K) (x' : A) : (term744 A K k x i x') = (term748 A K k x i x').
Proof. exact (MK_COMB (@lem4450516 K x k) (@lem4450511 A K k x i x')). Qed.
Lemma lem4450519 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4450520 {A K : Type'} (k : K -> Prop) (x : K) (i : K) (x' : A) : (term748 A K k x i x') = (term745 A K k x i x').
Proof. exact (@lem4450519 (term745 A K k x i x')). Qed.
Lemma lem4450521 {A K : Type'} (k : K -> Prop) (x : K) (i : K) (x' : A) : (term744 A K k x i x') = (term745 A K k x i x').
Proof. exact (TRANS (@lem4450517 A K k x i x') (@lem4450520 A K k x i x')). Qed.
Lemma lem4450536 {A K : Type'} (z : K -> A) (k : K -> Prop) (x : K) (i : K) (x' : A) : (term729 A K x' i k z x) = (term745 A K k x i x').
Proof. exact (TRANS (@lem4450508 A K z k x i x') (@lem4450521 A K k x i x')). Qed.
Lemma lem4450537 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (x' : K) : (term749 A K i x k z x') = (term749 A K i x k z x').
Proof. exact (eq_refl (term749 A K i x k z x')). Qed.
Lemma lem4450538 {A K : Type'} (z : K -> A) (k : K -> Prop) (x : K) (i : K) (x' : A) : ((term597 A K i x' k z x) = (term729 A K x' i k z x)) = ((term597 A K i x' k z x) = (term745 A K k x i x')).
Proof. exact (MK_COMB (@lem4450537 A K i x' k z x) (@lem4450536 A K z k x i x')). Qed.
Lemma lem4450539 {A K : Type'} (z : K -> A) (k : K -> Prop) (x : K) (i : K) (x' : A) : (term597 A K i x' k z x) = (term745 A K k x i x').
Proof. exact (EQ_MP (@lem4450538 A K z k x i x') (@lem4450348 A K x' i k z x)). Qed.
Lemma lem4450540 {A K : Type'} (z : K -> A) (k : K -> Prop) (i : K) (x : A) : (term599 A K i x k z) = (term750 A K k i x).
Proof. exact (fun_ext (fun x' : K => @lem4450539 A K z k x' i x)). Qed.
Lemma lem4450541 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4450542 {A K : Type'} (z : K -> A) (k : K -> Prop) (i : K) (x : A) : (term600 A K i x k z) = (term751 A K k i x).
Proof. exact (MK_COMB (@lem4450541 K) (@lem4450540 A K z k i x)). Qed.
Lemma lem4450543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4450544 {A K : Type'} (z : K -> A) (k : K -> Prop) (i : K) (x : A) : (term602 A K i x k z) = (term752 A K k i x).
Proof. exact (MK_COMB (@lem4450543) (@lem4450542 A K z k i x)). Qed.
Lemma lem4450545 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term614 A K i x k z s) = (term753 A K k x i z s).
Proof. exact (MK_COMB (@lem4450544 A K z k i x) (@lem4450279 A K k x i z s)). Qed.
Lemma lem4450546 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4450547 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term620 A K i x k z s) = (term754 A K k x i z s).
Proof. exact (MK_COMB (@lem4450546) (@lem4450545 A K k x i z s)). Qed.
Lemma lem4450548 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term629 A K k z s P i x) = (term755 A K k z s P i x).
Proof. exact (MK_COMB (@lem4450547 A K k x i z s) (@lem4450049 A K P i x)). Qed.
Lemma lem4450549 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4450550 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term631 A K k z s P i x) = (term756 A K k z s P i x).
Proof. exact (MK_COMB (@lem4450549) (@lem4450548 A K k z s P i x)). Qed.
Lemma lem4450551 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term633 A K k z s P i x) = (term757 A K k z s P i x).
Proof. exact (MK_COMB (@lem4450550 A K k z s P i x) (@lem4450048 A K P i x)). Qed.
Lemma lem4450554 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term641 A K x s i) = (term641 A K x s i).
Proof. exact (eq_refl (term641 A K x s i)). Qed.
Lemma lem4450555 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term643 A K k z s P i x) = (term758 A K k z s P i x).
Proof. exact (MK_COMB (@lem4450554 A K x s i) (@lem4450551 A K k z s P i x)). Qed.
Lemma lem4450558 {K : Type'} (i : K) (k : K -> Prop) : (term27 K i k) = (term27 K i k).
Proof. exact (eq_refl (term27 K i k)). Qed.
Lemma lem4450559 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term645 A K k z s P i x) = (term759 A K k z s P i x).
Proof. exact (MK_COMB (@lem4450558 K i k) (@lem4450555 A K k z s P i x)). Qed.
Lemma lem4450564 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term429 A K k z s i) = (term429 A K k z s i).
Proof. exact (eq_refl (term429 A K k z s i)). Qed.
Lemma lem4450565 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term430 A K k z s) = (term430 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4450564 A K k z s i)). Qed.
Lemma lem4450566 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4450567 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term431 A K k z s) = (term431 A K k z s).
Proof. exact (MK_COMB (@lem4450566 K) (@lem4450565 A K k z s)). Qed.
Lemma lem4450568 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4450569 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term545 A K k z s) = (term545 A K k z s).
Proof. exact (MK_COMB (@lem4450568) (@lem4450567 A K k z s)). Qed.
Lemma lem4450570 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term647 A K k z s P i x) = (term760 A K k z s P i x).
Proof. exact (MK_COMB (@lem4450569 A K k z s) (@lem4450559 A K k z s P i x)). Qed.
Lemma lem4450575 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term648 A K k s) = (term648 A K k s).
Proof. exact (eq_refl (term648 A K k s)). Qed.
Lemma lem4450576 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term649 A K k z s P i x) = (term761 A K k z s P i x).
Proof. exact (MK_COMB (@lem4450575 A K k s) (@lem4450570 A K k z s P i x)). Qed.
Lemma lem4450577 {A K : Type'} (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term651 A K z s P i x) = (term762 A K z s P i x).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4450576 A K k z s P i x)). Qed.
Lemma lem4450578 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4450579 {A K : Type'} (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term653 A K z s P i x) = (term763 A K z s P i x).
Proof. exact (MK_COMB (@lem4450578 K) (@lem4450577 A K z s P i x)). Qed.
Lemma lem4450580 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term655 A K s P i x) = (term764 A K s P i x).
Proof. exact (fun_ext (fun z : K -> A => @lem4450579 A K z s P i x)). Qed.
Lemma lem4450581 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4450582 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term657 A K s P i x) = (term765 A K s P i x).
Proof. exact (MK_COMB (@lem4450581 A K) (@lem4450580 A K s P i x)). Qed.
Lemma lem4450583 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (term659 A K P i x) = (term766 A K P i x).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4450582 A K s P i x)). Qed.
Lemma lem4450584 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4450585 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (term661 A K P i x) = (term767 A K P i x).
Proof. exact (MK_COMB (@lem4450584 A K) (@lem4450583 A K P i x)). Qed.
Lemma lem4450586 {A K : Type'} (i : K) (x : A) : (term663 A K i x) = (term768 A K i x).
Proof. exact (fun_ext (fun P : type1470 A K => @lem4450585 A K P i x)). Qed.
Lemma lem4450587 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4450588 {A K : Type'} (i : K) (x : A) : (term665 A K i x) = (term769 A K i x).
Proof. exact (MK_COMB (@lem4450587 A K) (@lem4450586 A K i x)). Qed.
Lemma lem4450589 {A K : Type'} (x : A) : (term667 A K x) = (term770 A K x).
Proof. exact (fun_ext (fun i : K => @lem4450588 A K i x)). Qed.
Lemma lem4450590 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4450591 {A K : Type'} (x : A) : (term669 A K x) = (term771 A K x).
Proof. exact (MK_COMB (@lem4450590 K) (@lem4450589 A K x)). Qed.
Lemma lem4450592 {A K : Type'} : (term671 A K) = (term772 A K).
Proof. exact (fun_ext (fun x : A => @lem4450591 A K x)). Qed.
Lemma lem4450593 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4450594 {A K : Type'} : (term673 A K) = (term773 A K).
Proof. exact (MK_COMB (@lem4450593 A) (@lem4450592 A K)). Qed.
Lemma lem4450679 {A K : Type'} : (term672 A K) = (term773 A K).
Proof. exact (TRANS (@lem4450047 A K) (@lem4450594 A K)). Qed.
Lemma lem4450680 {A K : Type'} : (term773 A K) = (term672 A K).
Proof. exact (SYM (@lem4450679 A K)). Qed.
Lemma lem4450682 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term431 A K k z s) : term431 A K k z s.
Proof. exact (h1). Qed.
Lemma lem4450685 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (h1 : term755 A K k z s P i x) : term755 A K k z s P i x.
Proof. exact (h1). Qed.
Lemma lem4450687 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4450688 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (P i x) = (term774 A K P i x).
Proof. exact (@lem4450687 (P i x)). Qed.
Lemma lem4450689 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (term774 A K P i x) = (P i x).
Proof. exact (SYM (@lem4450688 A K P i x)). Qed.
Lemma lem4450690 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) : term18 A K P i x.
Proof. exact (h1). Qed.
Lemma lem4450703 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term429 A K k z s i) = (term450 A K k z s i).
Proof. exact (@lem17265 (@IN K i k) (term451 A K z s i)). Qed.
Lemma lem4450704 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term430 A K k z s) = (term452 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4450703 A K k z s i)). Qed.
Lemma lem4450705 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4450758 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term431 A K k z s) = (term453 A K k z s).
Proof. exact (MK_COMB (@lem4450705 K) (@lem4450704 A K k z s)). Qed.
Lemma lem4450759 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term431 A K k z s) : term453 A K k z s.
Proof. exact (EQ_MP (@lem4450758 A K k z s) (@lem4450682 A K k z s h1)). Qed.
Lemma lem4450765 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4450771 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term15 A K x s i) : term15 A K x s i.
Proof. exact (h1). Qed.
Lemma lem4450775 {K : Type'} (x : K) (i : K) : (term775 K x i) = (x = i).
Proof. exact (@lem16933 (x = i)). Qed.
Lemma lem4450776 {A : Type'} (x : A) : (term776 A x) = (term776 A x).
Proof. exact (eq_refl (term776 A x)). Qed.
Lemma lem4450777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4450778 {K : Type'} (x : K) (i : K) : (term777 K x i) = (term778 K x i).
Proof. exact (MK_COMB (@lem4450777) (@lem4450775 K x i)). Qed.
Lemma lem4450779 {A K : Type'} (x : K) (i : K) (x' : A) : (term779 A K x i x') = (term780 A K x i x').
Proof. exact (MK_COMB (@lem4450778 K x i) (@lem4450776 A x')). Qed.
Lemma lem4450780 {A K : Type'} (x : K) (i : K) (x' : A) : (term781 A K x i x') = (term779 A K x i x').
Proof. exact (@lem17160 (term691 K x i) (x' = (@ARB A))). Qed.
Lemma lem4450781 {A K : Type'} (x : K) (i : K) (x' : A) : (term781 A K x i x') = (term780 A K x i x').
Proof. exact (TRANS (@lem4450780 A K x i x') (@lem4450779 A K x i x')). Qed.
Lemma lem4450783 {K : Type'} (x : K) (k : K -> Prop) : (term782 K x k) = (term782 K x k).
Proof. exact (eq_refl (term782 K x k)). Qed.
Lemma lem4450784 {A K : Type'} (k : K -> Prop) (x : K) (i : K) (x' : A) : (term783 A K k x i x') = (term784 A K k x i x').
Proof. exact (MK_COMB (@lem4450783 K x k) (@lem4450781 A K x i x')). Qed.
Lemma lem4450785 {A K : Type'} (k : K -> Prop) (x : K) (i : K) (x' : A) : (term785 A K k x i x') = (term783 A K k x i x').
Proof. exact (@lem17160 (@IN K x k) (term732 A K x i x')). Qed.
Lemma lem4450786 {A K : Type'} (k : K -> Prop) (x : K) (i : K) (x' : A) : (term785 A K k x i x') = (term784 A K k x i x').
Proof. exact (TRANS (@lem4450785 A K k x i x') (@lem4450784 A K k x i x')). Qed.
Lemma lem4450787 {K : Type'} (P : K -> Prop) : (term55 K P) = (term56 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4450788 {A K : Type'} (k : K -> Prop) (i : K) (x : A) : (term786 A K k i x) = (term787 A K k i x).
Proof. exact (@lem4450787 K (term750 A K k i x)). Qed.
Lemma lem4450789 {A K : Type'} (k : K -> Prop) (x : K) (i : K) (x' : A) : (term788 A K k i x' x) = (term745 A K k x i x').
Proof. exact (eq_refl (term788 A K k i x' x)). Qed.
Lemma lem4450790 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4450791 {A K : Type'} (k : K -> Prop) (x : K) (i : K) (x' : A) : (term789 A K k i x' x) = (term785 A K k x i x').
Proof. exact (MK_COMB (@lem4450790) (@lem4450789 A K k x i x')). Qed.
Lemma lem4450792 {A K : Type'} (k : K -> Prop) (x : K) (i : K) (x' : A) : (term789 A K k i x' x) = (term784 A K k x i x').
Proof. exact (TRANS (@lem4450791 A K k x i x') (@lem4450786 A K k x i x')). Qed.
Lemma lem4450793 {A K : Type'} (k : K -> Prop) (i : K) (x : A) : (term790 A K k i x) = (term791 A K k i x).
Proof. exact (fun_ext (fun x' : K => @lem4450792 A K k x' i x)). Qed.
Lemma lem4450794 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4450795 {A K : Type'} (k : K -> Prop) (i : K) (x : A) : (term787 A K k i x) = (term792 A K k i x).
Proof. exact (MK_COMB (@lem4450794 K) (@lem4450793 A K k i x)). Qed.
Lemma lem4450796 {A K : Type'} (k : K -> Prop) (i : K) (x : A) : (term786 A K k i x) = (term792 A K k i x).
Proof. exact (TRANS (@lem4450788 A K k i x) (@lem4450795 A K k i x)). Qed.
Lemma lem4450799 {K : Type'} (i' : K) (k : K -> Prop) : (term480 K i' k) = (@IN K i' k).
Proof. exact (@lem16933 (@IN K i' k)). Qed.
Lemma lem4450802 {K : Type'} (i' : K) (i : K) : (term775 K i' i) = (i' = i).
Proof. exact (@lem16933 (i' = i)). Qed.
Lemma lem4450803 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term474 A K x s i') = (term474 A K x s i').
Proof. exact (eq_refl (term474 A K x s i')). Qed.
Lemma lem4450804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4450805 {K : Type'} (i' : K) (i : K) : (term777 K i' i) = (term778 K i' i).
Proof. exact (MK_COMB (@lem4450804) (@lem4450802 K i' i)). Qed.
Lemma lem4450806 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term793 A K i x s i') = (term794 A K i x s i').
Proof. exact (MK_COMB (@lem4450805 K i' i) (@lem4450803 A K x s i')). Qed.
Lemma lem4450807 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term795 A K i x s i') = (term793 A K i x s i').
Proof. exact (@lem17160 (term691 K i' i) (term15 A K x s i')). Qed.
Lemma lem4450808 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term795 A K i x s i') = (term794 A K i x s i').
Proof. exact (TRANS (@lem4450807 A K i x s i') (@lem4450806 A K i x s i')). Qed.
Lemma lem4450815 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term796 A K i z s i') = (term797 A K i z s i').
Proof. exact (@lem17160 (i' = i) (term451 A K z s i')). Qed.
Lemma lem4450816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4450817 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term798 A K i x s i') = (term799 A K i x s i').
Proof. exact (MK_COMB (@lem4450816) (@lem4450808 A K i x s i')). Qed.
Lemma lem4450818 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term800 A K x i z s i') = (term801 A K x i z s i').
Proof. exact (MK_COMB (@lem4450817 A K i x s i') (@lem4450815 A K i z s i')). Qed.
Lemma lem4450819 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term802 A K x i z s i') = (term800 A K x i z s i').
Proof. exact (@lem17045 (term704 A K i x s i') (term709 A K i z s i')). Qed.
Lemma lem4450820 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term802 A K x i z s i') = (term801 A K x i z s i').
Proof. exact (TRANS (@lem4450819 A K x i z s i') (@lem4450818 A K x i z s i')). Qed.
Lemma lem4450821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4450822 {K : Type'} (i' : K) (k : K -> Prop) : (term501 K i' k) = (term2 K i' k).
Proof. exact (MK_COMB (@lem4450821) (@lem4450799 K i' k)). Qed.
Lemma lem4450823 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term803 A K k x i z s i') = (term804 A K k x i z s i').
Proof. exact (MK_COMB (@lem4450822 K i' k) (@lem4450820 A K x i z s i')). Qed.
Lemma lem4450824 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term805 A K k x i z s i') = (term803 A K k x i z s i').
Proof. exact (@lem17160 (term473 K i' k) (term710 A K x i z s i')). Qed.
Lemma lem4450825 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term805 A K k x i z s i') = (term804 A K k x i z s i').
Proof. exact (TRANS (@lem4450824 A K k x i z s i') (@lem4450823 A K k x i z s i')). Qed.
Lemma lem4450826 {K : Type'} (P : K -> Prop) : (term55 K P) = (term56 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4450827 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term806 A K k x i z s) = (term807 A K k x i z s).
Proof. exact (@lem4450826 K (term720 A K k x i z s)). Qed.
Lemma lem4450828 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term808 A K k x i z s i') = (term718 A K k x i z s i').
Proof. exact (eq_refl (term808 A K k x i z s i')). Qed.
Lemma lem4450829 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4450830 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term809 A K k x i z s i') = (term805 A K k x i z s i').
Proof. exact (MK_COMB (@lem4450829) (@lem4450828 A K k x i z s i')). Qed.
Lemma lem4450831 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term809 A K k x i z s i') = (term804 A K k x i z s i').
Proof. exact (TRANS (@lem4450830 A K k x i z s i') (@lem4450825 A K k x i z s i')). Qed.
Lemma lem4450832 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term810 A K k x i z s) = (term811 A K k x i z s).
Proof. exact (fun_ext (fun i' : K => @lem4450831 A K k x i z s i')). Qed.
Lemma lem4450833 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4450834 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term807 A K k x i z s) = (term812 A K k x i z s).
Proof. exact (MK_COMB (@lem4450833 K) (@lem4450832 A K k x i z s)). Qed.
Lemma lem4450835 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term806 A K k x i z s) = (term812 A K k x i z s).
Proof. exact (TRANS (@lem4450827 A K k x i z s) (@lem4450834 A K k x i z s)). Qed.
Lemma lem4450836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4450837 {A K : Type'} (k : K -> Prop) (i : K) (x : A) : (term813 A K k i x) = (term814 A K k i x).
Proof. exact (MK_COMB (@lem4450836) (@lem4450796 A K k i x)). Qed.
Lemma lem4450838 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term815 A K k x i z s) = (term816 A K k x i z s).
Proof. exact (MK_COMB (@lem4450837 A K k i x) (@lem4450835 A K k x i z s)). Qed.
Lemma lem4450839 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term817 A K k x i z s) = (term815 A K k x i z s).
Proof. exact (@lem17045 (term751 A K k i x) (term721 A K k x i z s)). Qed.
Lemma lem4450840 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term817 A K k x i z s) = (term816 A K k x i z s).
Proof. exact (TRANS (@lem4450839 A K k x i z s) (@lem4450838 A K k x i z s)). Qed.
Lemma lem4450841 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (P i x) = (P i x).
Proof. exact (eq_refl (P i x)). Qed.
Lemma lem4450842 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4450843 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term818 A K k x i z s) = (term819 A K k x i z s).
Proof. exact (MK_COMB (@lem4450842) (@lem4450840 A K k x i z s)). Qed.
Lemma lem4450844 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term820 A K k z s P i x) = (term821 A K k z s P i x).
Proof. exact (MK_COMB (@lem4450843 A K k x i z s) (@lem4450841 A K P i x)). Qed.
Lemma lem4450845 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term755 A K k z s P i x) = (term820 A K k z s P i x).
Proof. exact (@lem17265 (term753 A K k x i z s) (P i x)). Qed.
Lemma lem4450846 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term755 A K k z s P i x) = (term821 A K k z s P i x).
Proof. exact (TRANS (@lem4450845 A K k z s P i x) (@lem4450844 A K k z s P i x)). Qed.
Lemma lem4450945 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term133 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4450946 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term133 K P Q) = (term132 K P Q).
Proof. exact (@lem4450945 K P Q). Qed.
Lemma lem4450947 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term822 A K k x i z s) = (term823 A K k x i z s).
Proof. exact (@lem4450946 K (term791 A K k i x) (term811 A K k x i z s)). Qed.
Lemma lem4450948 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) : (term824 A K k i x i') = (term784 A K k i' i x).
Proof. exact (eq_refl (term824 A K k i x i')). Qed.
Lemma lem4450949 {A K : Type'} (k : K -> Prop) (i : K) (x : A) : (term825 A K k i x) = (term791 A K k i x).
Proof. exact (fun_ext (fun i' : K => @lem4450948 A K k i' i x)). Qed.
Lemma lem4450950 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4450951 {A K : Type'} (k : K -> Prop) (i : K) (x : A) : (term826 A K k i x) = (term792 A K k i x).
Proof. exact (MK_COMB (@lem4450950 K) (@lem4450949 A K k i x)). Qed.
Lemma lem4450952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4450953 {A K : Type'} (k : K -> Prop) (i : K) (x : A) : (term827 A K k i x) = (term814 A K k i x).
Proof. exact (MK_COMB (@lem4450952) (@lem4450951 A K k i x)). Qed.
Lemma lem4450954 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term828 A K k x i z s i') = (term804 A K k x i z s i').
Proof. exact (eq_refl (term828 A K k x i z s i')). Qed.
Lemma lem4450955 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term829 A K k x i z s) = (term811 A K k x i z s).
Proof. exact (fun_ext (fun i' : K => @lem4450954 A K k x i z s i')). Qed.
Lemma lem4450956 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4450957 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term830 A K k x i z s) = (term812 A K k x i z s).
Proof. exact (MK_COMB (@lem4450956 K) (@lem4450955 A K k x i z s)). Qed.
Lemma lem4450958 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term822 A K k x i z s) = (term816 A K k x i z s).
Proof. exact (MK_COMB (@lem4450953 A K k i x) (@lem4450957 A K k x i z s)). Qed.
Lemma lem4450959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4450960 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term831 A K k x i z s) = (term832 A K k x i z s).
Proof. exact (MK_COMB (@lem4450959) (@lem4450958 A K k x i z s)). Qed.
Lemma lem4450961 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) : (term824 A K k i x i') = (term784 A K k i' i x).
Proof. exact (eq_refl (term824 A K k i x i')). Qed.
Lemma lem4450962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4450963 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) : (term833 A K k i x i') = (term834 A K k i' i x).
Proof. exact (MK_COMB (@lem4450962) (@lem4450961 A K k i' i x)). Qed.
Lemma lem4450964 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term828 A K k x i z s i') = (term804 A K k x i z s i').
Proof. exact (eq_refl (term828 A K k x i z s i')). Qed.
Lemma lem4450965 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term835 A K k x i z s i') = (term836 A K k x i z s i').
Proof. exact (MK_COMB (@lem4450963 A K k i' i x) (@lem4450964 A K k x i z s i')). Qed.
Lemma lem4450966 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term837 A K k x i z s) = (term838 A K k x i z s).
Proof. exact (fun_ext (fun i' : K => @lem4450965 A K k x i z s i')). Qed.
Lemma lem4450967 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4450968 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term823 A K k x i z s) = (term839 A K k x i z s).
Proof. exact (MK_COMB (@lem4450967 K) (@lem4450966 A K k x i z s)). Qed.
Lemma lem4450969 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : ((term822 A K k x i z s) = (term823 A K k x i z s)) = ((term816 A K k x i z s) = (term839 A K k x i z s)).
Proof. exact (MK_COMB (@lem4450960 A K k x i z s) (@lem4450968 A K k x i z s)). Qed.
Lemma lem4450970 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term816 A K k x i z s) = (term839 A K k x i z s).
Proof. exact (EQ_MP (@lem4450969 A K k x i z s) (@lem4450947 A K k x i z s)). Qed.
Lemma lem4450973 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term840 A K k x i z s) = (term840 A K k x i z s).
Proof. exact (eq_refl (term840 A K k x i z s)). Qed.
Lemma lem4450974 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term840 A K k x i z s) = ((term816 A K k x i z s) = (term839 A K k x i z s)).
Proof. exact (eq_refl (term840 A K k x i z s)). Qed.
Lemma lem4450975 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term841 A K k x i z s) = (term841 A K k x i z s).
Proof. exact (eq_refl (term841 A K k x i z s)). Qed.
Lemma lem4450976 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : ((term840 A K k x i z s) = (term840 A K k x i z s)) = ((term840 A K k x i z s) = ((term816 A K k x i z s) = (term839 A K k x i z s))).
Proof. exact (MK_COMB (@lem4450975 A K k x i z s) (@lem4450974 A K k x i z s)). Qed.
Lemma lem4450977 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term840 A K k x i z s) = ((term816 A K k x i z s) = (term839 A K k x i z s)).
Proof. exact (eq_refl (term840 A K k x i z s)). Qed.
Lemma lem4450978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4450979 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term841 A K k x i z s) = (term842 A K k x i z s).
Proof. exact (MK_COMB (@lem4450978) (@lem4450977 A K k x i z s)). Qed.
Lemma lem4450980 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : ((term816 A K k x i z s) = (term839 A K k x i z s)) = ((term816 A K k x i z s) = (term839 A K k x i z s)).
Proof. exact (eq_refl ((term816 A K k x i z s) = (term839 A K k x i z s))). Qed.
Lemma lem4450981 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : ((term840 A K k x i z s) = ((term816 A K k x i z s) = (term839 A K k x i z s))) = (((term816 A K k x i z s) = (term839 A K k x i z s)) = ((term816 A K k x i z s) = (term839 A K k x i z s))).
Proof. exact (MK_COMB (@lem4450979 A K k x i z s) (@lem4450980 A K k x i z s)). Qed.
Lemma lem4450982 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : ((term840 A K k x i z s) = (term840 A K k x i z s)) = (((term816 A K k x i z s) = (term839 A K k x i z s)) = ((term816 A K k x i z s) = (term839 A K k x i z s))).
Proof. exact (TRANS (@lem4450976 A K k x i z s) (@lem4450981 A K k x i z s)). Qed.
Lemma lem4450983 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : ((term816 A K k x i z s) = (term839 A K k x i z s)) = ((term816 A K k x i z s) = (term839 A K k x i z s)).
Proof. exact (EQ_MP (@lem4450982 A K k x i z s) (@lem4450973 A K k x i z s)). Qed.
Lemma lem4450984 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term816 A K k x i z s) = (term839 A K k x i z s).
Proof. exact (EQ_MP (@lem4450983 A K k x i z s) (@lem4450970 A K k x i z s)). Qed.
Lemma lem4450985 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4450986 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term819 A K k x i z s) = (term843 A K k x i z s).
Proof. exact (MK_COMB (@lem4450985) (@lem4450984 A K k x i z s)). Qed.
Lemma lem4450987 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (P i x) = (P i x).
Proof. exact (eq_refl (P i x)). Qed.
Lemma lem4450988 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term821 A K k z s P i x) = (term844 A K k z s P i x).
Proof. exact (MK_COMB (@lem4450986 A K k x i z s) (@lem4450987 A K P i x)). Qed.
Lemma lem4450990 {A : Type'} (P : A -> Prop) (Q : Prop) : (term253 A P Q) = (term254 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4450991 {K : Type'} (P : K -> Prop) (Q : Prop) : (term253 K P Q) = (term254 K P Q).
Proof. exact (@lem4450990 K P Q). Qed.
Lemma lem4450992 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term845 A K k z s P i x) = (term846 A K k z s P i x).
Proof. exact (@lem4450991 K (term838 A K k x i z s) (P i x)). Qed.
Lemma lem4450993 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term847 A K k x i z s i') = (term836 A K k x i z s i').
Proof. exact (eq_refl (term847 A K k x i z s i')). Qed.
Lemma lem4450994 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term848 A K k x i z s) = (term838 A K k x i z s).
Proof. exact (fun_ext (fun i' : K => @lem4450993 A K k x i z s i')). Qed.
Lemma lem4450995 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4450996 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term849 A K k x i z s) = (term839 A K k x i z s).
Proof. exact (MK_COMB (@lem4450995 K) (@lem4450994 A K k x i z s)). Qed.
Lemma lem4450997 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4450998 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term850 A K k x i z s) = (term843 A K k x i z s).
Proof. exact (MK_COMB (@lem4450997) (@lem4450996 A K k x i z s)). Qed.
Lemma lem4450999 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (P i x) = (P i x).
Proof. exact (eq_refl (P i x)). Qed.
Lemma lem4451000 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term845 A K k z s P i x) = (term844 A K k z s P i x).
Proof. exact (MK_COMB (@lem4450998 A K k x i z s) (@lem4450999 A K P i x)). Qed.
Lemma lem4451001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4451002 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term851 A K k z s P i x) = (term852 A K k z s P i x).
Proof. exact (MK_COMB (@lem4451001) (@lem4451000 A K k z s P i x)). Qed.
Lemma lem4451003 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term847 A K k x i z s i') = (term836 A K k x i z s i').
Proof. exact (eq_refl (term847 A K k x i z s i')). Qed.
Lemma lem4451004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4451005 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term853 A K k x i z s i') = (term854 A K k x i z s i').
Proof. exact (MK_COMB (@lem4451004) (@lem4451003 A K k x i z s i')). Qed.
Lemma lem4451006 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (P i x) = (P i x).
Proof. exact (eq_refl (P i x)). Qed.
Lemma lem4451007 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (P : type1470 A K) (i : K) (x : A) : (term855 A K k z s i' P i x) = (term856 A K k z s i' P i x).
Proof. exact (MK_COMB (@lem4451005 A K k x i z s i') (@lem4451006 A K P i x)). Qed.
Lemma lem4451008 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term857 A K k z s P i x) = (term858 A K k z s P i x).
Proof. exact (fun_ext (fun i' : K => @lem4451007 A K k z s i' P i x)). Qed.
Lemma lem4451009 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4451010 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term846 A K k z s P i x) = (term859 A K k z s P i x).
Proof. exact (MK_COMB (@lem4451009 K) (@lem4451008 A K k z s P i x)). Qed.
Lemma lem4451011 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : ((term845 A K k z s P i x) = (term846 A K k z s P i x)) = ((term844 A K k z s P i x) = (term859 A K k z s P i x)).
Proof. exact (MK_COMB (@lem4451002 A K k z s P i x) (@lem4451010 A K k z s P i x)). Qed.
Lemma lem4451012 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term844 A K k z s P i x) = (term859 A K k z s P i x).
Proof. exact (EQ_MP (@lem4451011 A K k z s P i x) (@lem4450992 A K k z s P i x)). Qed.
Lemma lem4451014 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term821 A K k z s P i x) = (term859 A K k z s P i x).
Proof. exact (TRANS (@lem4450988 A K k z s P i x) (@lem4451012 A K k z s P i x)). Qed.
Lemma lem4451015 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term755 A K k z s P i x) = (term859 A K k z s P i x).
Proof. exact (TRANS (@lem4450846 A K k z s P i x) (@lem4451014 A K k z s P i x)). Qed.
Lemma lem4451016 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (h1 : term755 A K k z s P i x) : term859 A K k z s P i x.
Proof. exact (EQ_MP (@lem4451015 A K k z s P i x) (@lem4450685 A K k z s P i x h1)). Qed.
Lemma lem4451022 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) : term18 A K P i x.
Proof. exact (h1). Qed.
Lemma lem4451023 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (P : type1470 A K) (i : K) (x : A) (h1 : term856 A K k z s i' P i x) : term856 A K k z s i' P i x.
Proof. exact (h1). Qed.
Lemma lem4451044 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4451045 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4451044 K (A -> Prop) f x). Qed.
Lemma lem4451047 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4451045 A K s i). Qed.
Lemma lem4451048 {A K : Type'} (z : K -> A) (i : K) : (term457 A K z i) = (term457 A K z i).
Proof. exact (eq_refl (term457 A K z i)). Qed.
Lemma lem4451049 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) : (term451 A K z s i) = (term860 A K z s i).
Proof. exact (MK_COMB (@lem4451048 A K z i) (@lem4451047 A K s i)). Qed.
Lemma lem4451058 {K : Type'} (i : K) (k : K -> Prop) : (term460 K i k) = (term460 K i k).
Proof. exact (eq_refl (term460 K i k)). Qed.
Lemma lem4451059 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term450 A K k z s i) = (term861 A K k z s i).
Proof. exact (MK_COMB (@lem4451058 K i k) (@lem4451049 A K z s i)). Qed.
Lemma lem4451060 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term452 A K k z s) = (term862 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4451059 A K k z s i)). Qed.
Lemma lem4451061 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4451062 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term453 A K k z s) = (term863 A K k z s).
Proof. exact (MK_COMB (@lem4451061 K) (@lem4451060 A K k z s)). Qed.
Lemma lem4451063 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term431 A K k z s) : term863 A K k z s.
Proof. exact (EQ_MP (@lem4451062 A K k z s) (@lem4450759 A K k z s h1)). Qed.
Lemma lem4451069 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4451076 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4451077 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4451076 K (A -> Prop) f x). Qed.
Lemma lem4451079 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4451077 A K s i). Qed.
Lemma lem4451080 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4451081 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term15 A K x s i) = (term864 A K x s i).
Proof. exact (MK_COMB (@lem4451080 A x) (@lem4451079 A K s i)). Qed.
Lemma lem4451090 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) : term18 A K P i x.
Proof. exact (h1). Qed.
Lemma lem4451095 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (P i x) = (P i x).
Proof. exact (eq_refl (P i x)). Qed.
Lemma lem4451096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4451105 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4451106 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4451105 K (A -> Prop) f x). Qed.
Lemma lem4451108 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (@I (K -> A -> Prop) s i').
Proof. exact (@lem4451106 A K s i'). Qed.
Lemma lem4451109 {A K : Type'} (z : K -> A) (i' : K) : (term457 A K z i') = (term457 A K z i').
Proof. exact (eq_refl (term457 A K z i')). Qed.
Lemma lem4451110 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) : (term451 A K z s i') = (term860 A K z s i').
Proof. exact (MK_COMB (@lem4451109 A K z i') (@lem4451108 A K s i')). Qed.
Lemma lem4451111 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) : (term865 A K z s i') = (term866 A K z s i').
Proof. exact (MK_COMB (@lem4451096) (@lem4451110 A K z s i')). Qed.
Lemma lem4451120 {K : Type'} (i' : K) (i : K) : (term867 K i' i) = (term867 K i' i).
Proof. exact (eq_refl (term867 K i' i)). Qed.
Lemma lem4451121 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term797 A K i z s i') = (term868 A K i z s i').
Proof. exact (MK_COMB (@lem4451120 K i' i) (@lem4451111 A K z s i')). Qed.
Lemma lem4451122 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4451129 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4451130 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4451129 K (A -> Prop) f x). Qed.
Lemma lem4451132 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (@I (K -> A -> Prop) s i').
Proof. exact (@lem4451130 A K s i'). Qed.
Lemma lem4451133 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4451134 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term15 A K x s i') = (term864 A K x s i').
Proof. exact (MK_COMB (@lem4451133 A x) (@lem4451132 A K s i')). Qed.
Lemma lem4451135 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term474 A K x s i') = (term869 A K x s i').
Proof. exact (MK_COMB (@lem4451122) (@lem4451134 A K x s i')). Qed.
Lemma lem4451142 {K : Type'} (i' : K) (i : K) : (term778 K i' i) = (term778 K i' i).
Proof. exact (eq_refl (term778 K i' i)). Qed.
Lemma lem4451143 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term794 A K i x s i') = (term870 A K i x s i').
Proof. exact (MK_COMB (@lem4451142 K i' i) (@lem4451135 A K x s i')). Qed.
Lemma lem4451144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4451145 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term799 A K i x s i') = (term871 A K i x s i').
Proof. exact (MK_COMB (@lem4451144) (@lem4451143 A K i x s i')). Qed.
Lemma lem4451146 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term801 A K x i z s i') = (term872 A K x i z s i').
Proof. exact (MK_COMB (@lem4451145 A K i x s i') (@lem4451121 A K i z s i')). Qed.
Lemma lem4451153 {K : Type'} (i' : K) (k : K -> Prop) : (term2 K i' k) = (term2 K i' k).
Proof. exact (eq_refl (term2 K i' k)). Qed.
Lemma lem4451154 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term804 A K k x i z s i') = (term873 A K k x i z s i').
Proof. exact (MK_COMB (@lem4451153 K i' k) (@lem4451146 A K x i z s i')). Qed.
Lemma lem4451181 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) : (term834 A K k i' i x) = (term834 A K k i' i x).
Proof. exact (eq_refl (term834 A K k i' i x)). Qed.
Lemma lem4451182 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term836 A K k x i z s i') = (term874 A K k x i z s i').
Proof. exact (MK_COMB (@lem4451181 A K k i' i x) (@lem4451154 A K k x i z s i')). Qed.
Lemma lem4451183 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4451184 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term854 A K k x i z s i') = (term875 A K k x i z s i').
Proof. exact (MK_COMB (@lem4451183) (@lem4451182 A K k x i z s i')). Qed.
Lemma lem4451185 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (P : type1470 A K) (i : K) (x : A) : (term856 A K k z s i' P i x) = (term876 A K k z s i' P i x).
Proof. exact (MK_COMB (@lem4451184 A K k x i z s i') (@lem4451095 A K P i x)). Qed.
Lemma lem4451186 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (P : type1470 A K) (i : K) (x : A) (h1 : term856 A K k z s i' P i x) : term876 A K k z s i' P i x.
Proof. exact (EQ_MP (@lem4451185 A K k z s i' P i x) (@lem4451023 A K k z s i' P i x h1)). Qed.
Lemma lem4451187 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term874 A K k x i z s i') : term874 A K k x i z s i'.
Proof. exact (h1). Qed.
Lemma lem4451189 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term784 A K k i' i x) : term784 A K k i' i x.
Proof. exact (h1). Qed.
Lemma lem4451190 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term873 A K k x i z s i') : term873 A K k x i z s i'.
Proof. exact (h1). Qed.
Lemma lem4451191 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term784 A K k i' i x) : term780 A K i' i x.
Proof. exact (proj2 (@lem4451189 A K k i' i x h1)). Qed.
Lemma lem4451195 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term873 A K k x i z s i') : term872 A K x i z s i'.
Proof. exact (proj2 (@lem4451190 A K k x i z s i' h1)). Qed.
Lemma lem4451197 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term870 A K i x s i') : term870 A K i x s i'.
Proof. exact (h1). Qed.
Lemma lem4451198 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term868 A K i z s i') : term868 A K i z s i'.
Proof. exact (h1). Qed.
Lemma lem4451223 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4451296 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term861 A K k z s i) = (term861 A K k z s i).
Proof. exact (eq_refl (term861 A K k z s i)). Qed.
Lemma lem4451297 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term862 A K k z s) = (term862 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4451296 A K k z s i)). Qed.
Lemma lem4451298 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4451300 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term863 A K k z s) = (term863 A K k z s).
Proof. exact (MK_COMB (@lem4451298 K) (@lem4451297 A K k z s)). Qed.
Lemma lem4451301 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term431 A K k z s) : term863 A K k z s.
Proof. exact (EQ_MP (@lem4451300 A K k z s) (@lem4451063 A K k z s h1)). Qed.
Lemma lem4451354 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) : term18 A K P i x.
Proof. exact (h1). Qed.
Lemma lem4451358 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : P i x) : P i x.
Proof. exact (h1). Qed.
Lemma lem4451365 {A K : Type'} (_51399 : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term431 A K k z s) : term877 A K k z s _51399.
Proof. exact (@lem4451301 A K k z s h1 _51399). Qed.
Lemma lem4451366 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51399 : K) : (term877 A K k z s _51399) = (term861 A K k z s _51399).
Proof. exact (eq_refl (term877 A K k z s _51399)). Qed.
Lemma lem4451380 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4451386 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term784 A K k i' i x) : term473 K i' k.
Proof. exact (proj1 (@lem4451189 A K k i' i x h1)). Qed.
Lemma lem4451388 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term784 A K k i' i x) : i' = i.
Proof. exact (proj1 (@lem4451191 A K k i' i x h1)). Qed.
Lemma lem4451408 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term870 A K i x s i') : i' = i.
Proof. exact (proj1 (@lem4451197 A K i x s i' h1)). Qed.
Lemma lem4451410 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term870 A K i x s i') : term869 A K x s i'.
Proof. exact (proj2 (@lem4451197 A K i x s i' h1)). Qed.
Lemma lem4451418 {A K : Type'} (_51399 : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term431 A K k z s) : term861 A K k z s _51399.
Proof. exact (EQ_MP (@lem4451366 A K k z s _51399) (@lem4451365 A K _51399 k z s h1)). Qed.
Lemma lem4451430 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term868 A K i z s i') : term866 A K z s i'.
Proof. exact (proj2 (@lem4451198 A K i z s i' h1)). Qed.
Lemma lem4451444 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) : term18 A K P i x.
Proof. exact (h1). Qed.
Lemma lem4451446 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : P i x) : P i x.
Proof. exact (h1). Qed.
Lemma lem4451502 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4451531 {K : Type'} (k : K -> Prop) : (term878 K k) = (term878 K k).
Proof. exact (eq_refl (term878 K k)). Qed.
Lemma lem4451532 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term784 A K k i' i x) : (term879 K k i') = (term879 K k i).
Proof. exact (MK_COMB (@lem4451531 K k) (@lem4451388 A K k i' i x h1)). Qed.
Lemma lem4451533 {K : Type'} (i : K) (k : K -> Prop) : (term879 K k i) = (term473 K i k).
Proof. exact (eq_refl (term879 K k i)). Qed.
Lemma lem4451534 {K : Type'} (k : K -> Prop) (i' : K) : (term880 K k i') = (term880 K k i').
Proof. exact (eq_refl (term880 K k i')). Qed.
Lemma lem4451535 {K : Type'} (i' : K) (i : K) (k : K -> Prop) : ((term879 K k i') = (term879 K k i)) = ((term879 K k i') = (term473 K i k)).
Proof. exact (MK_COMB (@lem4451534 K k i') (@lem4451533 K i k)). Qed.
Lemma lem4451536 {K : Type'} (i' : K) (k : K -> Prop) : (term879 K k i') = (term473 K i' k).
Proof. exact (eq_refl (term879 K k i')). Qed.
Lemma lem4451537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4451538 {K : Type'} (i' : K) (k : K -> Prop) : (term880 K k i') = (term881 K i' k).
Proof. exact (MK_COMB (@lem4451537) (@lem4451536 K i' k)). Qed.
Lemma lem4451539 {K : Type'} (i : K) (k : K -> Prop) : (term473 K i k) = (term473 K i k).
Proof. exact (eq_refl (term473 K i k)). Qed.
Lemma lem4451540 {K : Type'} (i' : K) (i : K) (k : K -> Prop) : ((term879 K k i') = (term473 K i k)) = ((term473 K i' k) = (term473 K i k)).
Proof. exact (MK_COMB (@lem4451538 K i' k) (@lem4451539 K i k)). Qed.
Lemma lem4451541 {K : Type'} (i' : K) (i : K) (k : K -> Prop) : ((term879 K k i') = (term879 K k i)) = ((term473 K i' k) = (term473 K i k)).
Proof. exact (TRANS (@lem4451535 K i' i k) (@lem4451540 K i' i k)). Qed.
Lemma lem4451542 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term784 A K k i' i x) : (term473 K i' k) = (term473 K i k).
Proof. exact (EQ_MP (@lem4451541 K i' i k) (@lem4451532 A K k i' i x h1)). Qed.
Lemma lem4451543 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term784 A K k i' i x) : term473 K i k.
Proof. exact (EQ_MP (@lem4451542 A K k i' i x h1) (@lem4451386 A K k i' i x h1)). Qed.
Lemma lem4451655 {A K : Type'} (x : A) (s : type1470 A K) : (term882 A K x s) = (term882 A K x s).
Proof. exact (eq_refl (term882 A K x s)). Qed.
Lemma lem4451656 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term870 A K i x s i') : (term883 A K x s i') = (term883 A K x s i).
Proof. exact (MK_COMB (@lem4451655 A K x s) (@lem4451408 A K i x s i' h1)). Qed.
Lemma lem4451657 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term883 A K x s i) = (term869 A K x s i).
Proof. exact (eq_refl (term883 A K x s i)). Qed.
Lemma lem4451658 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term884 A K x s i') = (term884 A K x s i').
Proof. exact (eq_refl (term884 A K x s i')). Qed.
Lemma lem4451659 {A K : Type'} (i' : K) (x : A) (s : type1470 A K) (i : K) : ((term883 A K x s i') = (term883 A K x s i)) = ((term883 A K x s i') = (term869 A K x s i)).
Proof. exact (MK_COMB (@lem4451658 A K x s i') (@lem4451657 A K x s i)). Qed.
Lemma lem4451660 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term883 A K x s i') = (term869 A K x s i').
Proof. exact (eq_refl (term883 A K x s i')). Qed.
Lemma lem4451661 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4451662 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term884 A K x s i') = (term885 A K x s i').
Proof. exact (MK_COMB (@lem4451661) (@lem4451660 A K x s i')). Qed.
Lemma lem4451663 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term869 A K x s i) = (term869 A K x s i).
Proof. exact (eq_refl (term869 A K x s i)). Qed.
Lemma lem4451664 {A K : Type'} (i' : K) (x : A) (s : type1470 A K) (i : K) : ((term883 A K x s i') = (term869 A K x s i)) = ((term869 A K x s i') = (term869 A K x s i)).
Proof. exact (MK_COMB (@lem4451662 A K x s i') (@lem4451663 A K x s i)). Qed.
Lemma lem4451665 {A K : Type'} (i' : K) (x : A) (s : type1470 A K) (i : K) : ((term883 A K x s i') = (term883 A K x s i)) = ((term869 A K x s i') = (term869 A K x s i)).
Proof. exact (TRANS (@lem4451659 A K i' x s i) (@lem4451664 A K i' x s i)). Qed.
Lemma lem4451666 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term870 A K i x s i') : (term869 A K x s i') = (term869 A K x s i).
Proof. exact (EQ_MP (@lem4451665 A K i' x s i) (@lem4451656 A K i x s i' h1)). Qed.
Lemma lem4451667 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term870 A K i x s i') : term869 A K x s i.
Proof. exact (EQ_MP (@lem4451666 A K i x s i' h1) (@lem4451410 A K i x s i' h1)). Qed.
Lemma lem4451776 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4451777 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : term475 K i k.
Proof. exact (fun h0 : term473 K i k => @lem4451776 K i k h1). Qed.
Lemma lem4451779 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4451780 {K : Type'} (i : K) (k : K -> Prop) : (term475 K i k) = (@IN K i k).
Proof. exact (@lem4451779 (@IN K i k)). Qed.
Lemma lem4451781 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (EQ_MP (@lem4451780 K i k) (@lem4451777 K i k h1)). Qed.
Lemma lem4451784 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4451786 {K : Type'} (i : K) (k : K -> Prop) : (term473 K i k) = (term886 K i k).
Proof. exact (@lem4451784 (@IN K i k)). Qed.
Lemma lem4451789 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term784 A K k i' i x) : term886 K i k.
Proof. exact (EQ_MP (@lem4451786 K i k) (@lem4451543 A K k i' i x h1)). Qed.
Lemma lem4451792 {A K : Type'} (i' : K) (x : A) (i : K) (k : K -> Prop) (h1 : term784 A K k i' i x) (h2 : @IN K i k) : False.
Proof. exact (@lem4451789 A K k i' i x h1 (@lem4451781 K i k h2)). Qed.
Lemma lem4451793 {A K : Type'} (i' : K) (x : A) (i : K) (k : K -> Prop) (h1 : term784 A K k i' i x) (h2 : @IN K i k) : term324.
Proof. exact (fun h0 : ~ False => @lem4451792 A K i' x i k h1 h2). Qed.
Lemma lem4451795 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4451796 : term324 = False.
Proof. exact (@lem4451795 False). Qed.
Lemma lem4451797 {A K : Type'} (i' : K) (x : A) (i : K) (k : K -> Prop) (h1 : term784 A K k i' i x) (h2 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4451796) (@lem4451793 A K i' x i k h1 h2)). Qed.
Lemma lem4451906 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term15 A K x s i) : term864 A K x s i.
Proof. exact (EQ_MP (@lem4451081 A K x s i) (@lem4450771 A K x s i h1)). Qed.
Lemma lem4451907 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term15 A K x s i) : term887 A K x s i.
Proof. exact (fun h0 : term869 A K x s i => @lem4451906 A K x s i h1). Qed.
Lemma lem4451909 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4451910 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term887 A K x s i) = (term864 A K x s i).
Proof. exact (@lem4451909 (term864 A K x s i)). Qed.
Lemma lem4451911 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (h1 : term15 A K x s i) : term864 A K x s i.
Proof. exact (EQ_MP (@lem4451910 A K x s i) (@lem4451907 A K x s i h1)). Qed.
Lemma lem4451914 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4451916 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term869 A K x s i) = (term888 A K x s i).
Proof. exact (@lem4451914 (term864 A K x s i)). Qed.
Lemma lem4451919 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term870 A K i x s i') : term888 A K x s i.
Proof. exact (EQ_MP (@lem4451916 A K x s i) (@lem4451667 A K i x s i' h1)). Qed.
Lemma lem4451922 {A K : Type'} (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term870 A K i x s i') (h2 : term15 A K x s i) : False.
Proof. exact (@lem4451919 A K i x s i' h1 (@lem4451911 A K x s i h2)). Qed.
Lemma lem4451923 {A K : Type'} (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term870 A K i x s i') (h2 : term15 A K x s i) : term324.
Proof. exact (fun h0 : ~ False => @lem4451922 A K i' x s i h1 h2). Qed.
Lemma lem4451925 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4451926 : term324 = False.
Proof. exact (@lem4451925 False). Qed.
Lemma lem4452036 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term873 A K k x i z s i') : @IN K i' k.
Proof. exact (proj1 (@lem4451190 A K k x i z s i' h1)). Qed.
Lemma lem4452037 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term873 A K k x i z s i') : term475 K i' k.
Proof. exact (fun h0 : term473 K i' k => @lem4452036 A K k x i z s i' h1). Qed.
Lemma lem4452039 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4452040 {K : Type'} (i' : K) (k : K -> Prop) : (term475 K i' k) = (@IN K i' k).
Proof. exact (@lem4452039 (@IN K i' k)). Qed.
Lemma lem4452041 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term873 A K k x i z s i') : @IN K i' k.
Proof. exact (EQ_MP (@lem4452040 K i' k) (@lem4452037 A K k x i z s i' h1)). Qed.
Lemma lem4452047 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4452048 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51399 : K) (k : K -> Prop) : (term861 A K k z s _51399) = (term889 A K z s _51399 k).
Proof. exact (@lem4452047 (term860 A K z s _51399) (term473 K _51399 k)). Qed.
Lemma lem4452054 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4452055 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51399 : K) (k : K -> Prop) : (term890 A K k z s _51399) = (term891 A K z s _51399 k).
Proof. exact (MK_COMB (@lem4452054) (@lem4452048 A K z s _51399 k)). Qed.
Lemma lem4452061 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51399 : K) (k : K -> Prop) : (term889 A K z s _51399 k) = (term889 A K z s _51399 k).
Proof. exact (eq_refl (term889 A K z s _51399 k)). Qed.
Lemma lem4452062 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51399 : K) (k : K -> Prop) : ((term861 A K k z s _51399) = (term889 A K z s _51399 k)) = ((term889 A K z s _51399 k) = (term889 A K z s _51399 k)).
Proof. exact (MK_COMB (@lem4452055 A K z s _51399 k) (@lem4452061 A K z s _51399 k)). Qed.
Lemma lem4452064 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4452065 (x : Prop) : (x = x) = True.
Proof. exact (@lem4452064 Prop x). Qed.
Lemma lem4452066 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51399 : K) (k : K -> Prop) : ((term889 A K z s _51399 k) = (term889 A K z s _51399 k)) = True.
Proof. exact (@lem4452065 (term889 A K z s _51399 k)). Qed.
Lemma lem4452067 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51399 : K) (k : K -> Prop) : ((term861 A K k z s _51399) = (term889 A K z s _51399 k)) = True.
Proof. exact (TRANS (@lem4452062 A K z s _51399 k) (@lem4452066 A K z s _51399 k)). Qed.
Lemma lem4452068 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51399 : K) (k : K -> Prop) : True = ((term861 A K k z s _51399) = (term889 A K z s _51399 k)).
Proof. exact (SYM (@lem4452067 A K z s _51399 k)). Qed.
Lemma lem4452069 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51399 : K) (k : K -> Prop) : (term861 A K k z s _51399) = (term889 A K z s _51399 k).
Proof. exact (EQ_MP (@lem4452068 A K z s _51399 k) (@lem0)). Qed.
Lemma lem4452070 {A K : Type'} (_51399 : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term431 A K k z s) : term889 A K z s _51399 k.
Proof. exact (EQ_MP (@lem4452069 A K z s _51399 k) (@lem4451418 A K _51399 k z s h1)). Qed.
Lemma lem4452072 (b : Prop) (a : Prop) : (a \/ b) = (term315 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4452073 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51399 : K) : (term889 A K z s _51399 k) = (term892 A K k z s _51399).
Proof. exact (@lem4452072 (term473 K _51399 k) (term860 A K z s _51399)). Qed.
Lemma lem4452075 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4452076 {K : Type'} (_51399 : K) (k : K -> Prop) : (term480 K _51399 k) = (@IN K _51399 k).
Proof. exact (@lem4452075 (@IN K _51399 k)). Qed.
Lemma lem4452077 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4452078 {K : Type'} (_51399 : K) (k : K -> Prop) : (term481 K _51399 k) = (term27 K _51399 k).
Proof. exact (MK_COMB (@lem4452077) (@lem4452076 K _51399 k)). Qed.
Lemma lem4452079 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51399 : K) : (term860 A K z s _51399) = (term860 A K z s _51399).
Proof. exact (eq_refl (term860 A K z s _51399)). Qed.
Lemma lem4452080 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51399 : K) : (term892 A K k z s _51399) = (term893 A K k z s _51399).
Proof. exact (MK_COMB (@lem4452078 K _51399 k) (@lem4452079 A K z s _51399)). Qed.
Lemma lem4452081 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51399 : K) : (term889 A K z s _51399 k) = (term893 A K k z s _51399).
Proof. exact (TRANS (@lem4452073 A K k z s _51399) (@lem4452080 A K k z s _51399)). Qed.
Lemma lem4452084 {A K : Type'} (_51399 : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term431 A K k z s) : term893 A K k z s _51399.
Proof. exact (EQ_MP (@lem4452081 A K k z s _51399) (@lem4452070 A K _51399 k z s h1)). Qed.
Lemma lem4452085 {A K : Type'} (_51399 : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term431 A K k z s) : term893 A K k z s _51399.
Proof. exact (@lem4452084 A K _51399 k z s h1). Qed.
Lemma lem4452086 {A K : Type'} (i' : K) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term431 A K k z s) : term893 A K k z s i'.
Proof. exact (@lem4452085 A K i' k z s h1). Qed.
Lemma lem4452089 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term431 A K k z s) (h2 : term873 A K k x i z s i') : term860 A K z s i'.
Proof. exact (@lem4452086 A K i' k z s h1 (@lem4452041 A K k x i z s i' h2)). Qed.
Lemma lem4452090 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term431 A K k z s) (h2 : term873 A K k x i z s i') : term894 A K z s i'.
Proof. exact (fun h0 : term866 A K z s i' => @lem4452089 A K k x i z s i' h1 h2). Qed.
Lemma lem4452092 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4452093 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) : (term894 A K z s i') = (term860 A K z s i').
Proof. exact (@lem4452092 (term860 A K z s i')). Qed.
Lemma lem4452094 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term431 A K k z s) (h2 : term873 A K k x i z s i') : term860 A K z s i'.
Proof. exact (EQ_MP (@lem4452093 A K z s i') (@lem4452090 A K k x i z s i' h1 h2)). Qed.
Lemma lem4452097 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4452099 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) : (term866 A K z s i') = (term895 A K z s i').
Proof. exact (@lem4452097 (term860 A K z s i')). Qed.
Lemma lem4452102 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term868 A K i z s i') : term895 A K z s i'.
Proof. exact (EQ_MP (@lem4452099 A K z s i') (@lem4451430 A K i z s i' h1)). Qed.
Lemma lem4452105 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term431 A K k z s) (h2 : term868 A K i z s i') (h3 : term873 A K k x i z s i') : False.
Proof. exact (@lem4452102 A K i z s i' h2 (@lem4452094 A K k x i z s i' h1 h3)). Qed.
Lemma lem4452106 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term431 A K k z s) (h2 : term868 A K i z s i') (h3 : term873 A K k x i z s i') : term324.
Proof. exact (fun h0 : ~ False => @lem4452105 A K k x i z s i' h1 h2 h3). Qed.
Lemma lem4452108 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4452109 : term324 = False.
Proof. exact (@lem4452108 False). Qed.
Lemma lem4452110 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term431 A K k z s) (h2 : term868 A K i z s i') (h3 : term873 A K k x i z s i') : False.
Proof. exact (EQ_MP (@lem4452109) (@lem4452106 A K k x i z s i' h1 h2 h3)). Qed.
Lemma lem4452219 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : P i x) : P i x.
Proof. exact (h1). Qed.
Lemma lem4452220 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : P i x) : term896 A K P i x.
Proof. exact (fun h0 : term18 A K P i x => @lem4452219 A K P i x h1). Qed.
Lemma lem4452222 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4452223 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (term896 A K P i x) = (P i x).
Proof. exact (@lem4452222 (P i x)). Qed.
Lemma lem4452224 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : P i x) : P i x.
Proof. exact (EQ_MP (@lem4452223 A K P i x) (@lem4452220 A K P i x h1)). Qed.
Lemma lem4452227 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4452229 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (term18 A K P i x) = (term322 A K P i x).
Proof. exact (@lem4452227 (P i x)). Qed.
Lemma lem4452232 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) : term322 A K P i x.
Proof. exact (EQ_MP (@lem4452229 A K P i x) (@lem4451444 A K P i x h1)). Qed.
Lemma lem4452235 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : False.
Proof. exact (@lem4452232 A K P i x h1 (@lem4452224 A K P i x h2)). Qed.
Lemma lem4452236 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : term324.
Proof. exact (fun h0 : ~ False => @lem4452235 A K P i x h1 h2). Qed.
Lemma lem4452238 (p : Prop) : (term310 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4452239 : term324 = False.
Proof. exact (@lem4452238 False). Qed.
Lemma lem4452240 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : False.
Proof. exact (EQ_MP (@lem4452239) (@lem4452236 A K P i x h1 h2)). Qed.
Lemma lem4452241 {A K : Type'} (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term870 A K i x s i') (h2 : term15 A K x s i) : False.
Proof. exact (EQ_MP (@lem4451926) (@lem4451923 A K i' x s i h1 h2)). Qed.
Lemma lem4452242 {A K : Type'} (i' : K) (x : A) (i : K) (k : K -> Prop) (h1 : term784 A K k i' i x) (h2 : @IN K i k) : (@IN K i k) = False.
Proof. exact (prop_ext (fun h3 : @IN K i k => @lem4451797 A K i' x i k h1 h2) (fun h3 : False => @lem4451502 K i k h2)). Qed.
Lemma lem4452244 {A K : Type'} (i' : K) (x : A) (i : K) (k : K -> Prop) (h1 : term784 A K k i' i x) (h2 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4452242 A K i' x i k h1 h2) (@lem4451502 K i k h2)). Qed.
Lemma lem4452245 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : (P i x) = False.
Proof. exact (prop_ext (fun h3 : P i x => @lem4452240 A K P i x h1 h2) (fun h3 : False => @lem4451446 A K P i x h2)). Qed.
Lemma lem4452246 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : False.
Proof. exact (EQ_MP (@lem4452245 A K P i x h1 h2) (@lem4451446 A K P i x h2)). Qed.
Lemma lem4452247 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : (term18 A K P i x) = False.
Proof. exact (prop_ext (fun h3 : term18 A K P i x => @lem4452246 A K P i x h1 h2) (fun h3 : False => @lem4451444 A K P i x h1)). Qed.
Lemma lem4452248 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : False.
Proof. exact (EQ_MP (@lem4452247 A K P i x h1 h2) (@lem4451444 A K P i x h1)). Qed.
Lemma lem4452249 {A K : Type'} (i' : K) (x : A) (i : K) (k : K -> Prop) (h1 : term784 A K k i' i x) (h2 : @IN K i k) : (@IN K i k) = False.
Proof. exact (prop_ext (fun h3 : @IN K i k => @lem4452244 A K i' x i k h1 h2) (fun h3 : False => @lem4451380 K i k h2)). Qed.
Lemma lem4452250 {A K : Type'} (i' : K) (x : A) (i : K) (k : K -> Prop) (h1 : term784 A K k i' i x) (h2 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4452249 A K i' x i k h1 h2) (@lem4451380 K i k h2)). Qed.
Lemma lem4452251 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : (P i x) = False.
Proof. exact (prop_ext (fun h3 : P i x => @lem4452248 A K P i x h1 h2) (fun h3 : False => @lem4451358 A K P i x h2)). Qed.
Lemma lem4452252 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : False.
Proof. exact (EQ_MP (@lem4452251 A K P i x h1 h2) (@lem4451358 A K P i x h2)). Qed.
Lemma lem4452253 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : (term18 A K P i x) = False.
Proof. exact (prop_ext (fun h3 : term18 A K P i x => @lem4452252 A K P i x h1 h2) (fun h3 : False => @lem4451354 A K P i x h1)). Qed.
Lemma lem4452254 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : False.
Proof. exact (EQ_MP (@lem4452253 A K P i x h1 h2) (@lem4451354 A K P i x h1)). Qed.
Lemma lem4452255 {A K : Type'} (i' : K) (x : A) (i : K) (k : K -> Prop) (h1 : term784 A K k i' i x) (h2 : @IN K i k) : (@IN K i k) = False.
Proof. exact (prop_ext (fun h3 : @IN K i k => @lem4452250 A K i' x i k h1 h2) (fun h3 : False => @lem4451223 K i k h2)). Qed.
Lemma lem4452256 {A K : Type'} (i' : K) (x : A) (i : K) (k : K -> Prop) (h1 : term784 A K k i' i x) (h2 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4452255 A K i' x i k h1 h2) (@lem4451223 K i k h2)). Qed.
Lemma lem4452257 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : (P i x) = False.
Proof. exact (prop_ext (fun h3 : P i x => @lem4452254 A K P i x h1 h2) (fun h3 : False => @lem4451358 A K P i x h2)). Qed.
Lemma lem4452258 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : False.
Proof. exact (EQ_MP (@lem4452257 A K P i x h1 h2) (@lem4451358 A K P i x h2)). Qed.
Lemma lem4452259 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : (term18 A K P i x) = False.
Proof. exact (prop_ext (fun h3 : term18 A K P i x => @lem4452258 A K P i x h1 h2) (fun h3 : False => @lem4451354 A K P i x h1)). Qed.
Lemma lem4452260 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (h1 : term18 A K P i x) (h2 : P i x) : False.
Proof. exact (EQ_MP (@lem4452259 A K P i x h1 h2) (@lem4451354 A K P i x h1)). Qed.
Lemma lem4452261 {A K : Type'} (i' : K) (x : A) (i : K) (k : K -> Prop) (h1 : term784 A K k i' i x) (h2 : @IN K i k) : (@IN K i k) = False.
Proof. exact (prop_ext (fun h3 : @IN K i k => @lem4452256 A K i' x i k h1 h2) (fun h3 : False => @lem4451223 K i k h2)). Qed.
Lemma lem4452262 {A K : Type'} (i' : K) (x : A) (i : K) (k : K -> Prop) (h1 : term784 A K k i' i x) (h2 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4452261 A K i' x i k h1 h2) (@lem4451223 K i k h2)). Qed.
Lemma lem4452263 {A K : Type'} (k : K -> Prop) (z : K -> A) (i' : K) (x : A) (s : type1470 A K) (i : K) (h1 : term431 A K k z s) (h2 : term873 A K k x i z s i') (h3 : term15 A K x s i) : False.
Proof. exact (or_elim (@lem4451195 A K k x i z s i' h2) (fun h0 : term870 A K i x s i' => @lem4452241 A K i' x s i h0 h3) (fun h0 : term868 A K i z s i' => @lem4452110 A K k x i z s i' h1 h0 h2)). Qed.
Lemma lem4452264 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term431 A K k z s) (h2 : term15 A K x s i) (h3 : @IN K i k) (h4 : term874 A K k x i z s i') : False.
Proof. exact (or_elim (@lem4451187 A K k x i z s i' h4) (fun h0 : term784 A K k i' i x => @lem4452262 A K i' x i k h0 h3) (fun h0 : term873 A K k x i z s i' => @lem4452263 A K k z i' x s i h1 h0 h2)). Qed.
Lemma lem4452265 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (P : type1470 A K) (i : K) (x : A) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term15 A K x s i) (h4 : @IN K i k) (h5 : term856 A K k z s i' P i x) : False.
Proof. exact (or_elim (@lem4451186 A K k z s i' P i x h5) (fun h0 : term874 A K k x i z s i' => @lem4452264 A K k x i z s i' h1 h3 h4 h0) (fun h0 : P i x => @lem4452260 A K P i x h2 h0)). Qed.
Lemma lem4452266 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (P : type1470 A K) (i : K) (x : A) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term15 A K x s i) (h4 : @IN K i k) (h5 : term856 A K k z s i' P i x) : (term18 A K P i x) = False.
Proof. exact (prop_ext (fun h6 : term18 A K P i x => @lem4452265 A K k z s i' P i x h1 h2 h3 h4 h5) (fun h6 : False => @lem4451090 A K P i x h2)). Qed.
Lemma lem4452267 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (P : type1470 A K) (i : K) (x : A) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term15 A K x s i) (h4 : @IN K i k) (h5 : term856 A K k z s i' P i x) : False.
Proof. exact (EQ_MP (@lem4452266 A K k z s i' P i x h1 h2 h3 h4 h5) (@lem4451090 A K P i x h2)). Qed.
Lemma lem4452268 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (P : type1470 A K) (i : K) (x : A) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term15 A K x s i) (h4 : @IN K i k) (h5 : term856 A K k z s i' P i x) : (@IN K i k) = False.
Proof. exact (prop_ext (fun h6 : @IN K i k => @lem4452267 A K k z s i' P i x h1 h2 h3 h4 h5) (fun h6 : False => @lem4451069 K i k h4)). Qed.
Lemma lem4452269 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i' : K) (P : type1470 A K) (i : K) (x : A) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term15 A K x s i) (h4 : @IN K i k) (h5 : term856 A K k z s i' P i x) : False.
Proof. exact (EQ_MP (@lem4452268 A K k z s i' P i x h1 h2 h3 h4 h5) (@lem4451069 K i k h4)). Qed.
Lemma lem4452270 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term755 A K k z s P i x) (h4 : term15 A K x s i) (h5 : @IN K i k) : False.
Proof. exact (ex_elim (@lem4451016 A K k z s P i x h3) (fun i' : K => fun h0 : term858 A K k z s P i x i' => @lem4452269 A K k z s i' P i x h1 h2 h4 h5 h0)). Qed.
Lemma lem4452271 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term755 A K k z s P i x) (h4 : term15 A K x s i) (h5 : @IN K i k) : (term18 A K P i x) = False.
Proof. exact (prop_ext (fun h6 : term18 A K P i x => @lem4452270 A K z P x s i k h1 h2 h3 h4 h5) (fun h6 : False => @lem4451022 A K P i x h2)). Qed.
Lemma lem4452272 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term755 A K k z s P i x) (h4 : term15 A K x s i) (h5 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4452271 A K z P x s i k h1 h2 h3 h4 h5) (@lem4451022 A K P i x h2)). Qed.
Lemma lem4452273 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term755 A K k z s P i x) (h4 : term15 A K x s i) (h5 : @IN K i k) : (term15 A K x s i) = False.
Proof. exact (prop_ext (fun h6 : term15 A K x s i => @lem4452272 A K z P x s i k h1 h2 h3 h4 h5) (fun h6 : False => @lem4450771 A K x s i h4)). Qed.
Lemma lem4452274 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term755 A K k z s P i x) (h4 : term15 A K x s i) (h5 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4452273 A K z P x s i k h1 h2 h3 h4 h5) (@lem4450771 A K x s i h4)). Qed.
Lemma lem4452275 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term755 A K k z s P i x) (h4 : term15 A K x s i) (h5 : @IN K i k) : (@IN K i k) = False.
Proof. exact (prop_ext (fun h6 : @IN K i k => @lem4452274 A K z P x s i k h1 h2 h3 h4 h5) (fun h6 : False => @lem4450765 K i k h5)). Qed.
Lemma lem4452276 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term755 A K k z s P i x) (h4 : term15 A K x s i) (h5 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4452275 A K z P x s i k h1 h2 h3 h4 h5) (@lem4450765 K i k h5)). Qed.
Lemma lem4452277 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term755 A K k z s P i x) (h4 : term15 A K x s i) (h5 : @IN K i k) : (term18 A K P i x) = False.
Proof. exact (prop_ext (fun h6 : term18 A K P i x => @lem4452276 A K z P x s i k h1 h2 h3 h4 h5) (fun h6 : False => @lem4450690 A K P i x h2)). Qed.
Lemma lem4452278 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term18 A K P i x) (h3 : term755 A K k z s P i x) (h4 : term15 A K x s i) (h5 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4452277 A K z P x s i k h1 h2 h3 h4 h5) (@lem4450690 A K P i x h2)). Qed.
Lemma lem4452279 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term755 A K k z s P i x) (h3 : term15 A K x s i) (h4 : @IN K i k) : term774 A K P i x.
Proof. exact (fun h0 : term18 A K P i x => @lem4452278 A K z P x s i k h1 h0 h2 h3 h4). Qed.
Lemma lem4452280 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term755 A K k z s P i x) (h3 : term15 A K x s i) (h4 : @IN K i k) : P i x.
Proof. exact (EQ_MP (@lem4450689 A K P i x) (@lem4452279 A K z P x s i k h1 h2 h3 h4)). Qed.
Lemma lem4452281 {A K : Type'} (P : type1470 A K) (z : K -> A) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term15 A K x s i) (h3 : @IN K i k) : term757 A K k z s P i x.
Proof. exact (fun h0 : term755 A K k z s P i x => @lem4452280 A K z P x s i k h1 h0 h2 h3). Qed.
Lemma lem4452282 {A K : Type'} (P : type1470 A K) (x : A) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : @IN K i k) : term758 A K k z s P i x.
Proof. exact (fun h0 : term15 A K x s i => @lem4452281 A K P z x s i k h1 h0 h2). Qed.
Lemma lem4452283 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term431 A K k z s) : term759 A K k z s P i x.
Proof. exact (fun h0 : @IN K i k => @lem4452282 A K P x z s i k h1 h0). Qed.
Lemma lem4452284 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : term760 A K k z s P i x.
Proof. exact (fun h0 : term431 A K k z s => @lem4452283 A K P i x k z s h0). Qed.
Lemma lem4452285 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : term761 A K k z s P i x.
Proof. exact (fun h0 : term354 A K k s => @lem4452284 A K k z s P i x). Qed.
Lemma lem4452290 {A K : Type'} (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : term763 A K z s P i x.
Proof. exact (fun k : K -> Prop => @lem4452285 A K k z s P i x). Qed.
Lemma lem4452295 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : term765 A K s P i x.
Proof. exact (fun z : K -> A => @lem4452290 A K z s P i x). Qed.
Lemma lem4452300 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : term767 A K P i x.
Proof. exact (fun s : type1470 A K => @lem4452295 A K s P i x). Qed.
Lemma lem4452305 {A K : Type'} (i : K) (x : A) : term769 A K i x.
Proof. exact (fun P : type1470 A K => @lem4452300 A K P i x). Qed.
Lemma lem4452310 {A K : Type'} (x : A) : term771 A K x.
Proof. exact (fun i : K => @lem4452305 A K i x). Qed.
Lemma lem4452315 {A K : Type'} : term773 A K.
Proof. exact (fun x : A => @lem4452310 A K x). Qed.
Lemma lem4452316 {A K : Type'} : term672 A K.
Proof. exact (EQ_MP (@lem4450680 A K) (@lem4452315 A K)). Qed.
Lemma lem4452317 {A K : Type'} (x : A) : term897 A K x.
Proof. exact (@lem4452316 A K x). Qed.
Lemma lem4452318 {A K : Type'} (x : A) : (term897 A K x) = (term668 A K x).
Proof. exact (eq_refl (term897 A K x)). Qed.
Lemma lem4452319 {A K : Type'} (x : A) : term668 A K x.
Proof. exact (EQ_MP (@lem4452318 A K x) (@lem4452317 A K x)). Qed.
Lemma lem4452320 {A K : Type'} (x : A) (i : K) : term898 A K x i.
Proof. exact (@lem4452319 A K x i). Qed.
Lemma lem4452321 {A K : Type'} (i : K) (x : A) : (term898 A K x i) = (term664 A K i x).
Proof. exact (eq_refl (term898 A K x i)). Qed.
Lemma lem4452322 {A K : Type'} (i : K) (x : A) : term664 A K i x.
Proof. exact (EQ_MP (@lem4452321 A K i x) (@lem4452320 A K x i)). Qed.
Lemma lem4452323 {A K : Type'} (i : K) (x : A) (P : type1470 A K) : term899 A K i x P.
Proof. exact (@lem4452322 A K i x P). Qed.
Lemma lem4452324 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : (term899 A K i x P) = (term660 A K P i x).
Proof. exact (eq_refl (term899 A K i x P)). Qed.
Lemma lem4452325 {A K : Type'} (P : type1470 A K) (i : K) (x : A) : term660 A K P i x.
Proof. exact (EQ_MP (@lem4452324 A K P i x) (@lem4452323 A K i x P)). Qed.
Lemma lem4452326 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (s : type1470 A K) : term900 A K P i x s.
Proof. exact (@lem4452325 A K P i x s). Qed.
Lemma lem4452327 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term900 A K P i x s) = (term656 A K s P i x).
Proof. exact (eq_refl (term900 A K P i x s)). Qed.
Lemma lem4452328 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : term656 A K s P i x.
Proof. exact (EQ_MP (@lem4452327 A K s P i x) (@lem4452326 A K P i x s)). Qed.
Lemma lem4452329 {A K : Type'} (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (z : K -> A) : term901 A K s P i x z.
Proof. exact (@lem4452328 A K s P i x z). Qed.
Lemma lem4452330 {A K : Type'} (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term901 A K s P i x z) = (term652 A K z s P i x).
Proof. exact (eq_refl (term901 A K s P i x z)). Qed.
Lemma lem4452331 {A K : Type'} (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : term652 A K z s P i x.
Proof. exact (EQ_MP (@lem4452330 A K z s P i x) (@lem4452329 A K s P i x z)). Qed.
Lemma lem4452332 {A K : Type'} (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) (k : K -> Prop) : term902 A K z s P i x k.
Proof. exact (@lem4452331 A K z s P i x k). Qed.
Lemma lem4452333 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : (term902 A K z s P i x k) = (term636 A K k z s P i x).
Proof. exact (eq_refl (term902 A K z s P i x k)). Qed.
Lemma lem4452334 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : term636 A K k z s P i x.
Proof. exact (EQ_MP (@lem4452333 A K k z s P i x) (@lem4452332 A K z s P i x k)). Qed.
Lemma lem4452336 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (P : type1470 A K) (i : K) (x : A) : term636 A K k z s P i x.
Proof. exact (@lem4449922 A K k z s P i x (@lem4452334 A K k z s P i x)). Qed.
Lemma lem4452337 {A K : Type'} (z : K -> A) (P : type1470 A K) (i : K) (x : A) (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : term646 A K k z s P i x.
Proof. exact (@lem4452336 A K k z s P i x (@lem4448404 A K k s h1)). Qed.
Lemma lem4452338 {A K : Type'} (P : type1470 A K) (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term431 A K k z s) (h2 : term354 A K k s) : term644 A K k z s P i x.
Proof. exact (@lem4452337 A K z P i x k s h2 (@lem4449625 A K k z s h1)). Qed.
Lemma lem4452339 {A K : Type'} (P : type1470 A K) (x : A) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term354 A K k s) (h3 : @IN K i k) : term642 A K k z s P i x.
Proof. exact (@lem4452338 A K P i x z k s h1 h2 (@lem4449628 K i k h3)). Qed.
Lemma lem4452340 {A K : Type'} (P : type1470 A K) (z : K -> A) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term354 A K k s) (h3 : term15 A K x s i) (h4 : @IN K i k) : term634 A K k z s P i x.
Proof. exact (@lem4452339 A K P x z s i k h1 h2 h4 (@lem4449627 A K x s i h3)). Qed.
Lemma lem4452341 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term354 A K k s) (h3 : term635 A K k z s P i x) (h4 : term15 A K x s i) (h5 : @IN K i k) : False.
Proof. exact (@lem4452340 A K P z x s i k h1 h2 h4 h5 (@lem4449906 A K k z s P i x h3)). Qed.
Lemma lem4452342 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term354 A K k s) (h3 : term635 A K k z s P i x) (h4 : term15 A K x s i) (h5 : @IN K i k) : (term635 A K k z s P i x) = False.
Proof. exact (prop_ext (fun h6 : term635 A K k z s P i x => @lem4452341 A K z P x s i k h1 h2 h3 h4 h5) (fun h6 : False => @lem4449906 A K k z s P i x h3)). Qed.
Lemma lem4452343 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term354 A K k s) (h3 : term635 A K k z s P i x) (h4 : term15 A K x s i) (h5 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem4452342 A K z P x s i k h1 h2 h3 h4 h5) (@lem4449906 A K k z s P i x h3)). Qed.
Lemma lem4452344 {A K : Type'} (P : type1470 A K) (z : K -> A) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term354 A K k s) (h3 : term15 A K x s i) (h4 : @IN K i k) : term634 A K k z s P i x.
Proof. exact (fun h0 : term635 A K k z s P i x => @lem4452343 A K z P x s i k h1 h2 h0 h3 h4). Qed.
Lemma lem4452345 {A K : Type'} (P : type1470 A K) (z : K -> A) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term354 A K k s) (h3 : term15 A K x s i) (h4 : @IN K i k) : term633 A K k z s P i x.
Proof. exact (EQ_MP (@lem4449905 A K k z s P i x) (@lem4452344 A K P z x s i k h1 h2 h3 h4)). Qed.
Lemma lem4452346 {A K : Type'} (P : type1470 A K) (z : K -> A) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term354 A K k s) (h3 : term15 A K x s i) (h4 : @IN K i k) : term632 A K s k z P i x.
Proof. exact (EQ_MP (@lem4449901 A K s z P x i k h4) (@lem4452345 A K P z x s i k h1 h2 h3 h4)). Qed.
Lemma lem4452347 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term408 A K s k P) (h3 : term354 A K k s) (h4 : term15 A K x s i) (h5 : @IN K i k) : P i x.
Proof. exact (@lem4452346 A K P z x s i k h1 h3 h4 h5 (@lem4449634 A K x z i s k P h2)). Qed.
Lemma lem4452348 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (h1 : term445 A K k x s i) : term15 A K x s i.
Proof. exact (proj2 (@lem4449626 A K k x s i h1)). Qed.
Lemma lem4452349 {A K : Type'} (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (h1 : term445 A K k x s i) : @IN K i k.
Proof. exact (proj1 (@lem4449626 A K k x s i h1)). Qed.
Lemma lem4452350 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term408 A K s k P) (h3 : term354 A K k s) (h4 : term15 A K x s i) (h5 : @IN K i k) : (term15 A K x s i) = (P i x).
Proof. exact (prop_ext (fun h6 : term15 A K x s i => @lem4452347 A K z P x s i k h1 h2 h3 h4 h5) (fun h6 : P i x => @lem4449627 A K x s i h4)). Qed.
Lemma lem4452351 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term408 A K s k P) (h3 : term354 A K k s) (h4 : term15 A K x s i) (h5 : @IN K i k) : P i x.
Proof. exact (EQ_MP (@lem4452350 A K z P x s i k h1 h2 h3 h4 h5) (@lem4449627 A K x s i h4)). Qed.
Lemma lem4452352 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term408 A K s k P) (h3 : term354 A K k s) (h4 : term15 A K x s i) (h5 : @IN K i k) : (@IN K i k) = (P i x).
Proof. exact (prop_ext (fun h6 : @IN K i k => @lem4452351 A K z P x s i k h1 h2 h3 h4 h5) (fun h6 : P i x => @lem4449628 K i k h5)). Qed.
Lemma lem4452353 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term408 A K s k P) (h3 : term354 A K k s) (h4 : term15 A K x s i) (h5 : @IN K i k) : P i x.
Proof. exact (EQ_MP (@lem4452352 A K z P x s i k h1 h2 h3 h4 h5) (@lem4449628 K i k h5)). Qed.
Lemma lem4452354 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term408 A K s k P) (h3 : term354 A K k s) (h4 : term445 A K k x s i) (h5 : @IN K i k) : (term15 A K x s i) = (P i x).
Proof. exact (prop_ext (fun h6 : term15 A K x s i => @lem4452353 A K z P x s i k h1 h2 h3 h6 h5) (fun h6 : P i x => @lem4452348 A K k x s i h4)). Qed.
Lemma lem4452355 {A K : Type'} (z : K -> A) (P : type1470 A K) (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : term431 A K k z s) (h2 : term408 A K s k P) (h3 : term354 A K k s) (h4 : term445 A K k x s i) (h5 : @IN K i k) : P i x.
Proof. exact (EQ_MP (@lem4452354 A K z P x s i k h1 h2 h3 h4 h5) (@lem4452348 A K k x s i h4)). Qed.
Lemma lem4452356 {A K : Type'} (z : K -> A) (P : type1470 A K) (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (h1 : term431 A K k z s) (h2 : term408 A K s k P) (h3 : term354 A K k s) (h4 : term445 A K k x s i) : (@IN K i k) = (P i x).
Proof. exact (prop_ext (fun h5 : @IN K i k => @lem4452355 A K z P x s i k h1 h2 h3 h4 h5) (fun h5 : P i x => @lem4452349 A K k x s i h4)). Qed.
Lemma lem4452357 {A K : Type'} (z : K -> A) (P : type1470 A K) (k : K -> Prop) (x : A) (s : type1470 A K) (i : K) (h1 : term431 A K k z s) (h2 : term408 A K s k P) (h3 : term354 A K k s) (h4 : term445 A K k x s i) : P i x.
Proof. exact (EQ_MP (@lem4452356 A K z P k x s i h1 h2 h3 h4) (@lem4452349 A K k x s i h4)). Qed.
Lemma lem4452358 {A K : Type'} (i : K) (x : A) (z : K -> A) (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term431 A K k z s) (h2 : term408 A K s k P) (h3 : term354 A K k s) : term433 A K k s P i x.
Proof. exact (fun h0 : term445 A K k x s i => @lem4452357 A K z P k x s i h1 h2 h3 h0). Qed.
Lemma lem4452363 {A K : Type'} (i : K) (z : K -> A) (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term431 A K k z s) (h2 : term408 A K s k P) (h3 : term354 A K k s) : term435 A K k s P i.
Proof. exact (fun x : A => @lem4452358 A K i x z P k s h1 h2 h3). Qed.
Lemma lem4452368 {A K : Type'} (z : K -> A) (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term431 A K k z s) (h2 : term408 A K s k P) (h3 : term354 A K k s) : term377 A K k s P.
Proof. exact (fun i : K => @lem4452363 A K i z P k s h1 h2 h3). Qed.
Lemma lem4452369 {A K : Type'} (z : K -> A) (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term408 A K s k P) (h2 : term354 A K k s) : term547 A K z k s P.
Proof. exact (fun h0 : term431 A K k z s => @lem4452368 A K z P k s h0 h1 h2). Qed.
Lemma lem4452374 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term408 A K s k P) (h2 : term354 A K k s) : term550 A K k s P.
Proof. exact (fun z : K -> A => @lem4452369 A K z P k s h1 h2). Qed.
Lemma lem4452375 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term408 A K s k P) (h2 : term354 A K k s) : term532 A K k s P.
Proof. exact (EQ_MP (@lem4449624 A K k s P) (@lem4452374 A K P k s h1 h2)). Qed.
Lemma lem4452376 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term408 A K s k P) (h2 : term354 A K k s) : term377 A K k s P.
Proof. exact (@lem4452375 A K P k s h1 h2 (@lem4449512 A K k s h2)). Qed.
Lemma lem4452377 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : term903 A K k s P.
Proof. exact (fun h0 : term408 A K s k P => @lem4452376 A K P k s h0 h1). Qed.
Lemma lem4452378 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : term904 A K s k P.
Proof. exact (conj (@lem4452377 A K P k s h1) (@lem4449506 A K s k P)). Qed.
Lemma lem4452379 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term904 A K s k P) = ((term408 A K s k P) = (term377 A K k s P)).
Proof. exact (@lem32 (term408 A K s k P) (term377 A K k s P)). Qed.
Lemma lem4452380 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : (term408 A K s k P) = (term377 A K k s P).
Proof. exact (EQ_MP (@lem4452379 A K k s P) (@lem4452378 A K P k s h1)). Qed.
Lemma lem4452381 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : (term371 A K s k P) = (term377 A K k s P).
Proof. exact (EQ_MP (@lem4448688 A K k s P) (@lem4452380 A K P k s h1)). Qed.
Lemma lem4452382 {A K : Type'} (P : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term354 A K k s) : (term371 A K s k P) = (term378 A K k s P).
Proof. exact (EQ_MP (@lem4448581 A K P k s h1) (@lem4452381 A K P k s h1)). Qed.
Lemma lem4452383 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (P : type1470 A K) : (term371 A K s k P) = (term378 A K k s P).
Proof. exact (or_elim (@lem4448402 A K k s) (fun h0 : (@cartesian_product A K k s) = (@EMPTY (K -> A)) => @lem4448508 A K P k s h0) (fun h0 : term354 A K k s => @lem4452382 A K P k s h0)). Qed.
Lemma lem4452388 {A K : Type'} (k : K -> Prop) (P : type1470 A K) : term905 A K k P.
Proof. exact (fun s : type1470 A K => @lem4452383 A K k s P). Qed.
Lemma lem4452393 {A K : Type'} (P : type1470 A K) : term906 A K P.
Proof. exact (fun k : K -> Prop => @lem4452388 A K k P). Qed.
Lemma lem4452398 {A K : Type'} : term907 A K.
Proof. exact (fun P : type1470 A K => @lem4452393 A K P). Qed.

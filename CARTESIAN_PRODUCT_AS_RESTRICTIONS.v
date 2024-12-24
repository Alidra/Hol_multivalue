Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARTESIAN_PRODUCT_AS_RESTRICTIONS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSIONAL_spec.
Require Import FORALL_IN_GSPEC_spec.
Require Import FUN_EQ_THM_spec.
Require Import RESTRICTION_spec.
Require Import RESTRICTION_IN_CARTESIAN_PRODUCT_spec.
Require Import SUBSET_spec.
Require Import SUBSET_ANTISYM_EQ_spec.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184714_spec.
Require Import thm3184717_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Require Import thm7_spec.
Lemma lem4405012 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4382798 A B s). Qed.
Lemma lem4405013 {A B : Type'} (s : A -> Prop) : (term0 A B s) = ((@EXTENSIONAL A B s) = (term1 A B s)).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4405025 {_83152 : Type'} : term2 _83152.
Proof. exact (EQ_MP (@lem3184717 _83152) (@lem3184714 _83152)). Qed.
Lemma lem4405026 {_83152 : Type'} (p : _83152 -> Prop) : term3 _83152 p.
Proof. exact (@lem4405025 _83152 p). Qed.
Lemma lem4405027 {_83152 : Type'} (p : _83152 -> Prop) : (term3 _83152 p) = (term4 _83152 p).
Proof. exact (eq_refl (term3 _83152 p)). Qed.
Lemma lem4405028 {_83152 : Type'} (p : _83152 -> Prop) : term4 _83152 p.
Proof. exact (EQ_MP (@lem4405027 _83152 p) (@lem4405026 _83152 p)). Qed.
Lemma lem4405029 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term5 _83152 p x.
Proof. exact (@lem4405028 _83152 p x). Qed.
Lemma lem4405030 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term5 _83152 p x) = ((term6 _83152 p x) = (p x)).
Proof. exact (eq_refl (term5 _83152 p x)). Qed.
Lemma lem4405039 {_83095 : Type'} : term7 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4405040 {_83095 : Type'} (p : _83095 -> Prop) : term8 _83095 p.
Proof. exact (@lem4405039 _83095 p). Qed.
Lemma lem4405041 {_83095 : Type'} (p : _83095 -> Prop) : (term8 _83095 p) = (term9 _83095 p).
Proof. exact (eq_refl (term8 _83095 p)). Qed.
Lemma lem4405042 {_83095 : Type'} (p : _83095 -> Prop) : term9 _83095 p.
Proof. exact (EQ_MP (@lem4405041 _83095 p) (@lem4405040 _83095 p)). Qed.
Lemma lem4405043 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term10 _83095 p x.
Proof. exact (@lem4405042 _83095 p x). Qed.
Lemma lem4405044 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term10 _83095 p x) = ((term11 _83095 x p) = (p x)).
Proof. exact (eq_refl (term10 _83095 p x)). Qed.
Lemma lem4405046 {_83064 : Type'} : term12 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem4405047 {_83064 : Type'} (P : type919 _83064) : term13 _83064 P.
Proof. exact (@lem4405046 _83064 P). Qed.
Lemma lem4405048 {_83064 : Type'} (P : type919 _83064) : (term13 _83064 P) = (term14 _83064 P).
Proof. exact (eq_refl (term13 _83064 P)). Qed.
Lemma lem4405049 {_83064 : Type'} (P : type919 _83064) : term14 _83064 P.
Proof. exact (EQ_MP (@lem4405048 _83064 P) (@lem4405047 _83064 P)). Qed.
Lemma lem4405050 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term15 _83064 P x.
Proof. exact (@lem4405049 _83064 P x). Qed.
Lemma lem4405051 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term15 _83064 P x) = ((term16 _83064 x P) = (term17 _83064 P x)).
Proof. exact (eq_refl (term15 _83064 P x)). Qed.
Lemma lem4405053 {A K : Type'} (k : K -> Prop) : term18 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4405054 {A K : Type'} (k : K -> Prop) : (term18 A K k) = (term19 A K k).
Proof. exact (eq_refl (term18 A K k)). Qed.
Lemma lem4405055 {A K : Type'} (k : K -> Prop) : term19 A K k.
Proof. exact (EQ_MP (@lem4405054 A K k) (@lem4405053 A K k)). Qed.
Lemma lem4405056 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term20 A K k s.
Proof. exact (@lem4405055 A K k s). Qed.
Lemma lem4405057 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term20 A K k s) = ((@cartesian_product A K k s) = (term21 A K k s)).
Proof. exact (eq_refl (term20 A K k s)). Qed.
Lemma lem4405059 {A K : Type'} (k : K -> Prop) : term22 A K k.
Proof. exact (@lem4405001 A K k). Qed.
Lemma lem4405060 {A K : Type'} (k : K -> Prop) : (term22 A K k) = (term23 A K k).
Proof. exact (eq_refl (term22 A K k)). Qed.
Lemma lem4405061 {A K : Type'} (k : K -> Prop) : term23 A K k.
Proof. exact (EQ_MP (@lem4405060 A K k) (@lem4405059 A K k)). Qed.
Lemma lem4405062 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term24 A K k s.
Proof. exact (@lem4405061 A K k s). Qed.
Lemma lem4405063 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term24 A K k s) = (term25 A K k s).
Proof. exact (eq_refl (term24 A K k s)). Qed.
Lemma lem4405064 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term25 A K k s.
Proof. exact (EQ_MP (@lem4405063 A K k s) (@lem4405062 A K k s)). Qed.
Lemma lem4405065 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : term26 A K k s f.
Proof. exact (@lem4405064 A K k s f). Qed.
Lemma lem4405066 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term26 A K k s f) = ((term27 A K f k s) = (term28 A K k f s)).
Proof. exact (eq_refl (term26 A K k s f)). Qed.
Lemma lem4405070 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : (term29 A t s) = (s = t)) : (term29 A t s) = (s = t).
Proof. exact (h1). Qed.
Lemma lem4405071 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : (term29 A t s) = (s = t)) : (s = t) = (term29 A t s).
Proof. exact (SYM (@lem4405070 A s t h1)). Qed.
Lemma lem4405072 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : (s = t) = (term29 A t s)) : (s = t) = (term29 A t s).
Proof. exact (h1). Qed.
Lemma lem4405073 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : (s = t) = (term29 A t s)) : (term29 A t s) = (s = t).
Proof. exact (SYM (@lem4405072 A t s h1)). Qed.
Lemma lem4405074 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term29 A t s) = (s = t)) = ((s = t) = (term29 A t s)).
Proof. exact (prop_ext (fun h1 : (term29 A t s) = (s = t) => @lem4405071 A s t h1) (fun h1 : (s = t) = (term29 A t s) => @lem4405073 A t s h1)). Qed.
Lemma lem4405075 {A : Type'} (s : A -> Prop) : (term30 A s) = (term31 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4405074 A t s)). Qed.
Lemma lem4405076 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4405077 {A : Type'} (s : A -> Prop) : (term32 A s) = (term33 A s).
Proof. exact (MK_COMB (@lem4405076 A) (@lem4405075 A s)). Qed.
Lemma lem4405078 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4405077 A s)). Qed.
Lemma lem4405079 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4405080 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (MK_COMB (@lem4405079 A) (@lem4405078 A)). Qed.
Lemma lem4405081 {A : Type'} : term37 A.
Proof. exact (EQ_MP (@lem4405080 A) (@lem3219910 A)). Qed.
Lemma lem4405105 {_88905 _89106 : Type'} (Q : _89106 -> Prop) : term38 _88905 _89106 Q.
Proof. exact (proj1 (@lem3435744 _88905 Prop Prop Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem4405106 {_88905 _89106 : Type'} (Q : _89106 -> Prop) (P : _88905 -> Prop) : term39 _88905 _89106 Q P.
Proof. exact (@lem4405105 _88905 _89106 Q P). Qed.
Lemma lem4405107 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : (term39 _88905 _89106 Q P) = (term40 _88905 _89106 P Q).
Proof. exact (eq_refl (term39 _88905 _89106 Q P)). Qed.
Lemma lem4405108 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) : term40 _88905 _89106 P Q.
Proof. exact (EQ_MP (@lem4405107 _88905 _89106 P Q) (@lem4405106 _88905 _89106 Q P)). Qed.
Lemma lem4405109 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : term41 _88905 _89106 P Q f.
Proof. exact (@lem4405108 _88905 _89106 P Q f). Qed.
Lemma lem4405110 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term41 _88905 _89106 P Q f) = ((term42 _88905 _89106 P f Q) = (term43 _88905 _89106 P Q f)).
Proof. exact (eq_refl (term41 _88905 _89106 P Q f)). Qed.
Lemma lem4405112 {A : Type'} (s : A -> Prop) : term44 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4405113 {A : Type'} (s : A -> Prop) : (term44 A s) = (term45 A s).
Proof. exact (eq_refl (term44 A s)). Qed.
Lemma lem4405114 {A : Type'} (s : A -> Prop) : term45 A s.
Proof. exact (EQ_MP (@lem4405113 A s) (@lem4405112 A s)). Qed.
Lemma lem4405115 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term46 A s t.
Proof. exact (@lem4405114 A s t). Qed.
Lemma lem4405116 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term46 A s t) = ((@SUBSET A s t) = (term47 A s t)).
Proof. exact (eq_refl (term46 A s t)). Qed.
Lemma lem4405118 {A : Type'} (s : A -> Prop) : term48 A s.
Proof. exact (@lem4405081 A s). Qed.
Lemma lem4405119 {A : Type'} (s : A -> Prop) : (term48 A s) = (term33 A s).
Proof. exact (eq_refl (term48 A s)). Qed.
Lemma lem4405120 {A : Type'} (s : A -> Prop) : term33 A s.
Proof. exact (EQ_MP (@lem4405119 A s) (@lem4405118 A s)). Qed.
Lemma lem4405121 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term49 A s t.
Proof. exact (@lem4405120 A s t). Qed.
Lemma lem4405122 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term49 A s t) = ((s = t) = (term29 A t s)).
Proof. exact (eq_refl (term49 A s t)). Qed.
Lemma lem4405127 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term29 A t s).
Proof. exact (EQ_MP (@lem4405122 A t s) (@lem4405121 A s t)). Qed.
Lemma lem4405128 {A K : Type'} (t : type805 A K) (s : type805 A K) : (s = t) = (term50 A K t s).
Proof. exact (@lem4405127 (K -> A) t s). Qed.
Lemma lem4405129 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (term51 A K s k)) = (term52 A K k s).
Proof. exact (@lem4405128 A K (term51 A K s k) (@cartesian_product A K k s)). Qed.
Lemma lem4405133 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term47 A s t).
Proof. exact (EQ_MP (@lem4405116 A s t) (@lem4405115 A s t)). Qed.
Lemma lem4405134 {A K : Type'} (s : type805 A K) (t : type805 A K) : (@SUBSET (K -> A) s t) = (term53 A K s t).
Proof. exact (@lem4405133 (K -> A) s t). Qed.
Lemma lem4405135 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term54 A K s k) = (term55 A K s k).
Proof. exact (@lem4405134 A K (@cartesian_product A K k s) (term51 A K s k)). Qed.
Lemma lem4405152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4405153 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term56 A K s k) = (term57 A K s k).
Proof. exact (MK_COMB (@lem4405152) (@lem4405135 A K s k)). Qed.
Lemma lem4405155 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term47 A s t).
Proof. exact (EQ_MP (@lem4405116 A s t) (@lem4405115 A s t)). Qed.
Lemma lem4405156 {A K : Type'} (s : type805 A K) (t : type805 A K) : (@SUBSET (K -> A) s t) = (term53 A K s t).
Proof. exact (@lem4405155 (K -> A) s t). Qed.
Lemma lem4405157 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term58 A K k s) = (term59 A K k s).
Proof. exact (@lem4405156 A K (term51 A K s k) (@cartesian_product A K k s)). Qed.
Lemma lem4405159 {_88905 _89106 : Type'} (P : _88905 -> Prop) (Q : _89106 -> Prop) (f : _88905 -> _89106) : (term42 _88905 _89106 P f Q) = (term43 _88905 _89106 P Q f).
Proof. exact (EQ_MP (@lem4405110 _88905 _89106 P Q f) (@lem4405109 _88905 _89106 P Q f)). Qed.
Lemma lem4405160 {A K : Type'} (P : type805 A K) (Q : type805 A K) (f : type796 A K) : (term60 A K P f Q) = (term61 A K P Q f).
Proof. exact (@lem4405159 (K -> A) (K -> A) P Q f). Qed.
Lemma lem4405161 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term62 A K k s) = (term63 A K s k).
Proof. exact (@lem4405160 A K (term64 A K k s) (term65 A K k s) (term66 A K k)). Qed.
Lemma lem4405162 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term67 A K k s f) = (term28 A K k f s).
Proof. exact (eq_refl (term67 A K k s f)). Qed.
Lemma lem4405163 {A K : Type'} (GEN_PVAR_142 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_142) = (@SETSPEC (K -> A) GEN_PVAR_142).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_142)). Qed.
Lemma lem4405164 {A K : Type'} (GEN_PVAR_142 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term68 A K GEN_PVAR_142 k s f) = (term69 A K GEN_PVAR_142 k f s).
Proof. exact (MK_COMB (@lem4405163 A K GEN_PVAR_142) (@lem4405162 A K k f s)). Qed.
Lemma lem4405165 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term70 A K k f) = (@RESTRICTION K A k f).
Proof. exact (eq_refl (term70 A K k f)). Qed.
Lemma lem4405166 {A K : Type'} (GEN_PVAR_142 : K -> A) (s : type1470 A K) (k : K -> Prop) (f : K -> A) : (term71 A K GEN_PVAR_142 s k f) = (term72 A K GEN_PVAR_142 s k f).
Proof. exact (MK_COMB (@lem4405164 A K GEN_PVAR_142 k f s) (@lem4405165 A K k f)). Qed.
Lemma lem4405167 {A K : Type'} (GEN_PVAR_142 : K -> A) (s : type1470 A K) (k : K -> Prop) : (term73 A K GEN_PVAR_142 s k) = (term74 A K GEN_PVAR_142 s k).
Proof. exact (fun_ext (fun f : K -> A => @lem4405166 A K GEN_PVAR_142 s k f)). Qed.
Lemma lem4405168 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4405169 {A K : Type'} (GEN_PVAR_142 : K -> A) (s : type1470 A K) (k : K -> Prop) : (term75 A K GEN_PVAR_142 s k) = (term76 A K GEN_PVAR_142 s k).
Proof. exact (MK_COMB (@lem4405168 A K) (@lem4405167 A K GEN_PVAR_142 s k)). Qed.
Lemma lem4405170 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term77 A K s k) = (term78 A K s k).
Proof. exact (fun_ext (fun GEN_PVAR_142 : K -> A => @lem4405169 A K GEN_PVAR_142 s k)). Qed.
Lemma lem4405171 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4405172 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term79 A K s k) = (term51 A K s k).
Proof. exact (MK_COMB (@lem4405171 A K) (@lem4405170 A K s k)). Qed.
Lemma lem4405173 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4405174 {A K : Type'} (x : K -> A) (s : type1470 A K) (k : K -> Prop) : (term80 A K x s k) = (term81 A K x s k).
Proof. exact (MK_COMB (@lem4405173 A K x) (@lem4405172 A K s k)). Qed.
Lemma lem4405175 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4405176 {A K : Type'} (x : K -> A) (s : type1470 A K) (k : K -> Prop) : (term82 A K x s k) = (term83 A K x s k).
Proof. exact (MK_COMB (@lem4405175) (@lem4405174 A K x s k)). Qed.
Lemma lem4405177 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term84 A K k s x) = (term85 A K x k s).
Proof. exact (eq_refl (term84 A K k s x)). Qed.
Lemma lem4405178 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term86 A K k s x) = (term87 A K x k s).
Proof. exact (MK_COMB (@lem4405176 A K x s k) (@lem4405177 A K x k s)). Qed.
Lemma lem4405179 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term88 A K k s) = (term89 A K k s).
Proof. exact (fun_ext (fun x : K -> A => @lem4405178 A K x k s)). Qed.
Lemma lem4405180 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4405181 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term62 A K k s) = (term59 A K k s).
Proof. exact (MK_COMB (@lem4405180 A K) (@lem4405179 A K k s)). Qed.
Lemma lem4405182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4405183 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term90 A K k s) = (term91 A K k s).
Proof. exact (MK_COMB (@lem4405182) (@lem4405181 A K k s)). Qed.
Lemma lem4405184 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term67 A K k s f) = (term28 A K k f s).
Proof. exact (eq_refl (term67 A K k s f)). Qed.
Lemma lem4405185 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4405186 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term92 A K k s f) = (term93 A K k f s).
Proof. exact (MK_COMB (@lem4405185) (@lem4405184 A K k f s)). Qed.
Lemma lem4405187 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term94 A K s k f) = (term95 A K f k s).
Proof. exact (eq_refl (term94 A K s k f)). Qed.
Lemma lem4405188 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term96 A K s k f) = (term97 A K f k s).
Proof. exact (MK_COMB (@lem4405186 A K k f s) (@lem4405187 A K f k s)). Qed.
Lemma lem4405189 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term98 A K s k) = (term99 A K k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4405188 A K f k s)). Qed.
Lemma lem4405190 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4405191 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term63 A K s k) = (term100 A K k s).
Proof. exact (MK_COMB (@lem4405190 A K) (@lem4405189 A K k s)). Qed.
Lemma lem4405192 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term62 A K k s) = (term63 A K s k)) = ((term59 A K k s) = (term100 A K k s)).
Proof. exact (MK_COMB (@lem4405183 A K k s) (@lem4405191 A K k s)). Qed.
Lemma lem4405193 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term59 A K k s) = (term100 A K k s).
Proof. exact (EQ_MP (@lem4405192 A K k s) (@lem4405161 A K s k)). Qed.
Lemma lem4405198 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term58 A K k s) = (term100 A K k s).
Proof. exact (TRANS (@lem4405157 A K k s) (@lem4405193 A K k s)). Qed.
Lemma lem4405208 {A B : Type'} (f : A -> B) (y : A) : (term101 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4405209 {A K : Type'} (f : type796 A K) (y : K -> A) : (term102 A K f y) = (f y).
Proof. exact (@lem4405208 (K -> A) (K -> A) f y). Qed.
Lemma lem4405210 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term103 A K k f) = (term70 A K k f).
Proof. exact (@lem4405209 A K (term66 A K k) f). Qed.
Lemma lem4405211 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term70 A K k f) = (@RESTRICTION K A k f).
Proof. exact (eq_refl (term70 A K k f)). Qed.
Lemma lem4405212 {A K : Type'} (k : K -> Prop) : (term104 A K k) = (term66 A K k).
Proof. exact (fun_ext (fun f : K -> A => @lem4405211 A K k f)). Qed.
Lemma lem4405213 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4405214 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term103 A K k f) = (term70 A K k f).
Proof. exact (MK_COMB (@lem4405212 A K k) (@lem4405213 A K f)). Qed.
Lemma lem4405215 {A K : Type'} : (@eq (K -> A)) = (@eq (K -> A)).
Proof. exact (eq_refl (@eq (K -> A))). Qed.
Lemma lem4405216 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term105 A K k f) = (term106 A K k f).
Proof. exact (MK_COMB (@lem4405215 A K) (@lem4405214 A K k f)). Qed.
Lemma lem4405217 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term70 A K k f) = (@RESTRICTION K A k f).
Proof. exact (eq_refl (term70 A K k f)). Qed.
Lemma lem4405218 {A K : Type'} (k : K -> Prop) (f : K -> A) : ((term103 A K k f) = (term70 A K k f)) = ((term70 A K k f) = (@RESTRICTION K A k f)).
Proof. exact (MK_COMB (@lem4405216 A K k f) (@lem4405217 A K k f)). Qed.
Lemma lem4405219 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term70 A K k f) = (@RESTRICTION K A k f).
Proof. exact (EQ_MP (@lem4405218 A K k f) (@lem4405210 A K k f)). Qed.
Lemma lem4405220 {A K : Type'} : (@IN (K -> A)) = (@IN (K -> A)).
Proof. exact (eq_refl (@IN (K -> A))). Qed.
Lemma lem4405221 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term107 A K k f) = (term108 A K k f).
Proof. exact (MK_COMB (@lem4405220 A K) (@lem4405219 A K k f)). Qed.
Lemma lem4405222 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (@cartesian_product A K k s).
Proof. exact (eq_refl (@cartesian_product A K k s)). Qed.
Lemma lem4405223 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term95 A K f k s) = (term27 A K f k s).
Proof. exact (MK_COMB (@lem4405221 A K k f) (@lem4405222 A K k s)). Qed.
Lemma lem4405224 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term93 A K k f s) = (term93 A K k f s).
Proof. exact (eq_refl (term93 A K k f s)). Qed.
Lemma lem4405225 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term97 A K f k s) = (term109 A K f k s).
Proof. exact (MK_COMB (@lem4405224 A K k f s) (@lem4405223 A K f k s)). Qed.
Lemma lem4405228 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term99 A K k s) = (term110 A K k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4405225 A K f k s)). Qed.
Lemma lem4405229 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4405230 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term100 A K k s) = (term111 A K k s).
Proof. exact (MK_COMB (@lem4405229 A K) (@lem4405228 A K k s)). Qed.
Lemma lem4405235 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term58 A K k s) = (term111 A K k s).
Proof. exact (TRANS (@lem4405198 A K k s) (@lem4405230 A K k s)). Qed.
Lemma lem4405236 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term52 A K k s) = (term112 A K k s).
Proof. exact (MK_COMB (@lem4405153 A K s k) (@lem4405235 A K k s)). Qed.
Lemma lem4405239 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (term51 A K s k)) = (term112 A K k s).
Proof. exact (TRANS (@lem4405129 A K k s) (@lem4405236 A K k s)). Qed.
Lemma lem4405240 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term112 A K k s) = ((@cartesian_product A K k s) = (term51 A K s k)).
Proof. exact (SYM (@lem4405239 A K k s)). Qed.
Lemma lem4405272 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term27 A K f k s) = (term28 A K k f s).
Proof. exact (EQ_MP (@lem4405066 A K k f s) (@lem4405065 A K k s f)). Qed.
Lemma lem4405273 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term27 A K f k s) = (term28 A K k f s).
Proof. exact (@lem4405272 A K k f s). Qed.
Lemma lem4405280 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term93 A K k f s) = (term93 A K k f s).
Proof. exact (eq_refl (term93 A K k f s)). Qed.
Lemma lem4405281 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term109 A K f k s) = (term113 A K k f s).
Proof. exact (MK_COMB (@lem4405280 A K k f s) (@lem4405273 A K k f s)). Qed.
Lemma lem4405283 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem4405284 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term113 A K k f s) = True.
Proof. exact (@lem4405283 (term28 A K k f s)). Qed.
Lemma lem4405285 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term109 A K f k s) = True.
Proof. exact (TRANS (@lem4405281 A K k f s) (@lem4405284 A K k f s)). Qed.
Lemma lem4405286 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term110 A K k s) = (term114 A K).
Proof. exact (fun_ext (fun f : K -> A => @lem4405285 A K f k s)). Qed.
Lemma lem4405287 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4405288 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term111 A K k s) = (term115 A K).
Proof. exact (MK_COMB (@lem4405287 A K) (@lem4405286 A K k s)). Qed.
Lemma lem4405290 {A : Type'} (t : Prop) : (term116 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4405291 {A K : Type'} (t : Prop) : (term117 A K t) = t.
Proof. exact (@lem4405290 (K -> A) t). Qed.
Lemma lem4405292 {A K : Type'} : (term115 A K) = True.
Proof. exact (@lem4405291 A K True). Qed.
Lemma lem4405293 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term111 A K k s) = True.
Proof. exact (TRANS (@lem4405288 A K k s) (@lem4405292 A K)). Qed.
Lemma lem4405294 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term57 A K s k) = (term57 A K s k).
Proof. exact (eq_refl (term57 A K s k)). Qed.
Lemma lem4405295 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term112 A K k s) = (term118 A K s k).
Proof. exact (MK_COMB (@lem4405294 A K s k) (@lem4405293 A K k s)). Qed.
Lemma lem4405297 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4405298 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term118 A K s k) = (term55 A K s k).
Proof. exact (@lem4405297 (term55 A K s k)). Qed.
Lemma lem4405315 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term112 A K k s) = (term55 A K s k).
Proof. exact (TRANS (@lem4405295 A K s k) (@lem4405298 A K s k)). Qed.
Lemma lem4405316 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term55 A K s k) = (term112 A K k s).
Proof. exact (SYM (@lem4405315 A K s k)). Qed.
Lemma lem4405320 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term21 A K k s).
Proof. exact (EQ_MP (@lem4405057 A K k s) (@lem4405056 A K k s)). Qed.
Lemma lem4405321 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term21 A K k s).
Proof. exact (@lem4405320 A K k s). Qed.
Lemma lem4405329 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term1 A B s).
Proof. exact (EQ_MP (@lem4405013 A B s) (@lem4405012 A B s)). Qed.
Lemma lem4405330 {A K : Type'} (s : K -> Prop) : (@EXTENSIONAL K A s) = (term119 A K s).
Proof. exact (@lem4405329 K A s). Qed.
Lemma lem4405331 {A K : Type'} (k : K -> Prop) : (@EXTENSIONAL K A k) = (term119 A K k).
Proof. exact (@lem4405330 A K k). Qed.
Lemma lem4405344 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4405345 {A K : Type'} (k : K -> Prop) (f : K -> A) : (@EXTENSIONAL K A k f) = (term120 A K k f).
Proof. exact (MK_COMB (@lem4405331 A K k) (@lem4405344 A K f)). Qed.
Lemma lem4405347 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term6 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4405030 _83152 p x) (@lem4405029 _83152 p x)). Qed.
Lemma lem4405348 {A K : Type'} (p : type805 A K) (x : K -> A) : (term121 A K p x) = (p x).
Proof. exact (@lem4405347 (K -> A) p x). Qed.
Lemma lem4405349 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term122 A K k f) = (term123 A K k f).
Proof. exact (@lem4405348 A K (term124 A K k) f). Qed.
Lemma lem4405350 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term123 A K k f) = (term125 A K k f).
Proof. exact (eq_refl (term123 A K k f)). Qed.
Lemma lem4405351 {A K : Type'} (GEN_PVAR_139 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_139) = (@SETSPEC (K -> A) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_139)). Qed.
Lemma lem4405352 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term126 A K GEN_PVAR_139 k f) = (term127 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4405351 A K GEN_PVAR_139) (@lem4405350 A K k f)). Qed.
Lemma lem4405353 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4405354 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term128 A K GEN_PVAR_139 k f) = (term129 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4405352 A K GEN_PVAR_139 k f) (@lem4405353 A K f)). Qed.
Lemma lem4405355 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term130 A K GEN_PVAR_139 k) = (term131 A K GEN_PVAR_139 k).
Proof. exact (fun_ext (fun f : K -> A => @lem4405354 A K GEN_PVAR_139 k f)). Qed.
Lemma lem4405356 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4405357 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term132 A K GEN_PVAR_139 k) = (term133 A K GEN_PVAR_139 k).
Proof. exact (MK_COMB (@lem4405356 A K) (@lem4405355 A K GEN_PVAR_139 k)). Qed.
Lemma lem4405358 {A K : Type'} (k : K -> Prop) : (term134 A K k) = (term135 A K k).
Proof. exact (fun_ext (fun GEN_PVAR_139 : K -> A => @lem4405357 A K GEN_PVAR_139 k)). Qed.
Lemma lem4405359 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4405360 {A K : Type'} (k : K -> Prop) : (term136 A K k) = (term119 A K k).
Proof. exact (MK_COMB (@lem4405359 A K) (@lem4405358 A K k)). Qed.
Lemma lem4405361 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4405362 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term122 A K k f) = (term120 A K k f).
Proof. exact (MK_COMB (@lem4405360 A K k) (@lem4405361 A K f)). Qed.
Lemma lem4405363 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4405364 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term137 A K k f) = (term138 A K k f).
Proof. exact (MK_COMB (@lem4405363) (@lem4405362 A K k f)). Qed.
Lemma lem4405365 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term123 A K k f) = (term125 A K k f).
Proof. exact (eq_refl (term123 A K k f)). Qed.
Lemma lem4405366 {A K : Type'} (k : K -> Prop) (f : K -> A) : ((term122 A K k f) = (term123 A K k f)) = ((term120 A K k f) = (term125 A K k f)).
Proof. exact (MK_COMB (@lem4405364 A K k f) (@lem4405365 A K k f)). Qed.
Lemma lem4405367 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term120 A K k f) = (term125 A K k f).
Proof. exact (EQ_MP (@lem4405366 A K k f) (@lem4405349 A K k f)). Qed.
Lemma lem4405376 {A K : Type'} (k : K -> Prop) (f : K -> A) : (@EXTENSIONAL K A k f) = (term125 A K k f).
Proof. exact (TRANS (@lem4405345 A K k f) (@lem4405367 A K k f)). Qed.
Lemma lem4405377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4405378 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term139 A K k f) = (term140 A K k f).
Proof. exact (MK_COMB (@lem4405377) (@lem4405376 A K k f)). Qed.
Lemma lem4405385 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term28 A K k f s) = (term28 A K k f s).
Proof. exact (eq_refl (term28 A K k f s)). Qed.
Lemma lem4405386 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term141 A K k f s) = (term142 A K k f s).
Proof. exact (MK_COMB (@lem4405378 A K k f) (@lem4405385 A K k f s)). Qed.
Lemma lem4405389 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4405390 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term143 A K GEN_PVAR_140 k f s) = (term144 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4405389 A K GEN_PVAR_140) (@lem4405386 A K k f s)). Qed.
Lemma lem4405391 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4405392 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term145 A K GEN_PVAR_140 k s f) = (term146 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4405390 A K GEN_PVAR_140 k f s) (@lem4405391 A K f)). Qed.
Lemma lem4405393 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term147 A K GEN_PVAR_140 k s) = (term148 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4405392 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4405394 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4405395 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term149 A K GEN_PVAR_140 k s) = (term150 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4405394 A K) (@lem4405393 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4405400 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term151 A K k s) = (term152 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4405395 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4405401 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4405402 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term21 A K k s) = (term153 A K k s).
Proof. exact (MK_COMB (@lem4405401 A K) (@lem4405400 A K k s)). Qed.
Lemma lem4405403 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term153 A K k s).
Proof. exact (TRANS (@lem4405321 A K k s) (@lem4405402 A K k s)). Qed.
Lemma lem4405404 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4405405 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term85 A K x k s) = (term154 A K x k s).
Proof. exact (MK_COMB (@lem4405404 A K x) (@lem4405403 A K k s)). Qed.
Lemma lem4405407 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term11 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4405044 _83095 p x) (@lem4405043 _83095 p x)). Qed.
Lemma lem4405408 {A K : Type'} (p : type805 A K) (x : K -> A) : (term155 A K x p) = (p x).
Proof. exact (@lem4405407 (K -> A) p x). Qed.
Lemma lem4405409 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term156 A K x k s) = (term157 A K k s x).
Proof. exact (@lem4405408 A K (term158 A K k s) x). Qed.
Lemma lem4405410 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term157 A K k s f) = (term142 A K k f s).
Proof. exact (eq_refl (term157 A K k s f)). Qed.
Lemma lem4405411 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4405412 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term159 A K GEN_PVAR_140 k s f) = (term144 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4405411 A K GEN_PVAR_140) (@lem4405410 A K k f s)). Qed.
Lemma lem4405413 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4405414 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term160 A K GEN_PVAR_140 k s f) = (term146 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4405412 A K GEN_PVAR_140 k f s) (@lem4405413 A K f)). Qed.
Lemma lem4405415 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term161 A K GEN_PVAR_140 k s) = (term148 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4405414 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4405416 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4405417 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term162 A K GEN_PVAR_140 k s) = (term150 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4405416 A K) (@lem4405415 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4405418 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term163 A K k s) = (term152 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4405417 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4405419 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4405420 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term164 A K k s) = (term153 A K k s).
Proof. exact (MK_COMB (@lem4405419 A K) (@lem4405418 A K k s)). Qed.
Lemma lem4405421 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4405422 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term156 A K x k s) = (term154 A K x k s).
Proof. exact (MK_COMB (@lem4405421 A K x) (@lem4405420 A K k s)). Qed.
Lemma lem4405423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4405424 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term165 A K x k s) = (term166 A K x k s).
Proof. exact (MK_COMB (@lem4405423) (@lem4405422 A K x k s)). Qed.
Lemma lem4405425 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term157 A K k s x) = (term142 A K k x s).
Proof. exact (eq_refl (term157 A K k s x)). Qed.
Lemma lem4405426 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term156 A K x k s) = (term157 A K k s x)) = ((term154 A K x k s) = (term142 A K k x s)).
Proof. exact (MK_COMB (@lem4405424 A K x k s) (@lem4405425 A K k x s)). Qed.
Lemma lem4405427 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term154 A K x k s) = (term142 A K k x s).
Proof. exact (EQ_MP (@lem4405426 A K k x s) (@lem4405409 A K k s x)). Qed.
Lemma lem4405444 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term85 A K x k s) = (term142 A K k x s).
Proof. exact (TRANS (@lem4405405 A K x k s) (@lem4405427 A K k x s)). Qed.
Lemma lem4405445 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4405446 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term167 A K x k s) = (term168 A K k x s).
Proof. exact (MK_COMB (@lem4405445) (@lem4405444 A K k x s)). Qed.
Lemma lem4405450 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term16 _83064 x P) = (term17 _83064 P x).
Proof. exact (EQ_MP (@lem4405051 _83064 P x) (@lem4405050 _83064 P x)). Qed.
Lemma lem4405451 {A K : Type'} (P : type910 A K) (x : K -> A) : (term169 A K x P) = (term170 A K P x).
Proof. exact (@lem4405450 (K -> A) P x). Qed.
Lemma lem4405452 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term171 A K x s k) = (term172 A K s k x).
Proof. exact (@lem4405451 A K (term173 A K s k) x). Qed.
Lemma lem4405453 {A K : Type'} (GEN_PVAR_142 : K -> A) (s : type1470 A K) (k : K -> Prop) : (term174 A K s k GEN_PVAR_142) = (term76 A K GEN_PVAR_142 s k).
Proof. exact (eq_refl (term174 A K s k GEN_PVAR_142)). Qed.
Lemma lem4405454 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term175 A K s k) = (term78 A K s k).
Proof. exact (fun_ext (fun GEN_PVAR_142 : K -> A => @lem4405453 A K GEN_PVAR_142 s k)). Qed.
Lemma lem4405455 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4405456 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term176 A K s k) = (term51 A K s k).
Proof. exact (MK_COMB (@lem4405455 A K) (@lem4405454 A K s k)). Qed.
Lemma lem4405457 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4405458 {A K : Type'} (x : K -> A) (s : type1470 A K) (k : K -> Prop) : (term171 A K x s k) = (term81 A K x s k).
Proof. exact (MK_COMB (@lem4405457 A K x) (@lem4405456 A K s k)). Qed.
Lemma lem4405459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4405460 {A K : Type'} (x : K -> A) (s : type1470 A K) (k : K -> Prop) : (term177 A K x s k) = (term178 A K x s k).
Proof. exact (MK_COMB (@lem4405459) (@lem4405458 A K x s k)). Qed.
Lemma lem4405461 {A K : Type'} (x : K -> A) (s : type1470 A K) (k : K -> Prop) : (term172 A K s k x) = (term179 A K x s k).
Proof. exact (eq_refl (term172 A K s k x)). Qed.
Lemma lem4405462 {A K : Type'} (x : K -> A) (s : type1470 A K) (k : K -> Prop) : ((term171 A K x s k) = (term172 A K s k x)) = ((term81 A K x s k) = (term179 A K x s k)).
Proof. exact (MK_COMB (@lem4405460 A K x s k) (@lem4405461 A K x s k)). Qed.
Lemma lem4405463 {A K : Type'} (x : K -> A) (s : type1470 A K) (k : K -> Prop) : (term81 A K x s k) = (term179 A K x s k).
Proof. exact (EQ_MP (@lem4405462 A K x s k) (@lem4405452 A K s k x)). Qed.
Lemma lem4405469 {A B : Type'} (f : A -> B) (y : A) : (term101 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4405470 {A K : Type'} (f : type1528 A K) (y : Prop) : (term180 A K f y) = (f y).
Proof. exact (@lem4405469 Prop (type805 A K) f y). Qed.
Lemma lem4405471 {A K : Type'} (x : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term181 A K x k f s) = (term182 A K x k f s).
Proof. exact (@lem4405470 A K (term183 A K x) (term28 A K k f s)). Qed.
Lemma lem4405472 {A K : Type'} (p : Prop) (x : K -> A) : (term184 A K x p) = (term185 A K p x).
Proof. exact (eq_refl (term184 A K x p)). Qed.
Lemma lem4405473 {A K : Type'} (x : K -> A) : (term186 A K x) = (term183 A K x).
Proof. exact (fun_ext (fun p : Prop => @lem4405472 A K p x)). Qed.
Lemma lem4405474 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term28 A K k f s) = (term28 A K k f s).
Proof. exact (eq_refl (term28 A K k f s)). Qed.
Lemma lem4405475 {A K : Type'} (x : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term181 A K x k f s) = (term182 A K x k f s).
Proof. exact (MK_COMB (@lem4405473 A K x) (@lem4405474 A K k f s)). Qed.
Lemma lem4405476 {A K : Type'} : (@eq ((K -> A) -> Prop)) = (@eq ((K -> A) -> Prop)).
Proof. exact (eq_refl (@eq ((K -> A) -> Prop))). Qed.
Lemma lem4405477 {A K : Type'} (x : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term187 A K x k f s) = (term188 A K x k f s).
Proof. exact (MK_COMB (@lem4405476 A K) (@lem4405475 A K x k f s)). Qed.
Lemma lem4405478 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (x : K -> A) : (term182 A K x k f s) = (term189 A K k f s x).
Proof. exact (eq_refl (term182 A K x k f s)). Qed.
Lemma lem4405479 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (x : K -> A) : ((term181 A K x k f s) = (term182 A K x k f s)) = ((term182 A K x k f s) = (term189 A K k f s x)).
Proof. exact (MK_COMB (@lem4405477 A K x k f s) (@lem4405478 A K k f s x)). Qed.
Lemma lem4405480 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (x : K -> A) : (term182 A K x k f s) = (term189 A K k f s x).
Proof. exact (EQ_MP (@lem4405479 A K k f s x) (@lem4405471 A K x k f s)). Qed.
Lemma lem4405491 {A K : Type'} (k : K -> Prop) (f : K -> A) : (@RESTRICTION K A k f) = (@RESTRICTION K A k f).
Proof. exact (eq_refl (@RESTRICTION K A k f)). Qed.
Lemma lem4405492 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (f : K -> A) : (term190 A K x s k f) = (term191 A K s x k f).
Proof. exact (MK_COMB (@lem4405480 A K k f s x) (@lem4405491 A K k f)). Qed.
Lemma lem4405494 {A B : Type'} (f : A -> B) (y : A) : (term101 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4405495 {A K : Type'} (f : type805 A K) (y : K -> A) : (term192 A K f y) = (f y).
Proof. exact (@lem4405494 (K -> A) Prop f y). Qed.
Lemma lem4405496 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (f : K -> A) : (term193 A K s x k f) = (term191 A K s x k f).
Proof. exact (@lem4405495 A K (term189 A K k f s x) (@RESTRICTION K A k f)). Qed.
Lemma lem4405497 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (x : K -> A) (t : K -> A) : (term194 A K k f s x t) = (term195 A K k f s x t).
Proof. exact (eq_refl (term194 A K k f s x t)). Qed.
Lemma lem4405498 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (x : K -> A) : (term196 A K k f s x) = (term189 A K k f s x).
Proof. exact (fun_ext (fun t : K -> A => @lem4405497 A K k f s x t)). Qed.
Lemma lem4405499 {A K : Type'} (k : K -> Prop) (f : K -> A) : (@RESTRICTION K A k f) = (@RESTRICTION K A k f).
Proof. exact (eq_refl (@RESTRICTION K A k f)). Qed.
Lemma lem4405500 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (f : K -> A) : (term193 A K s x k f) = (term191 A K s x k f).
Proof. exact (MK_COMB (@lem4405498 A K k f s x) (@lem4405499 A K k f)). Qed.
Lemma lem4405501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4405502 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (f : K -> A) : (term197 A K s x k f) = (term198 A K s x k f).
Proof. exact (MK_COMB (@lem4405501) (@lem4405500 A K s x k f)). Qed.
Lemma lem4405503 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (f : K -> A) : (term191 A K s x k f) = (term199 A K s x k f).
Proof. exact (eq_refl (term191 A K s x k f)). Qed.
Lemma lem4405504 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (f : K -> A) : ((term193 A K s x k f) = (term191 A K s x k f)) = ((term191 A K s x k f) = (term199 A K s x k f)).
Proof. exact (MK_COMB (@lem4405502 A K s x k f) (@lem4405503 A K s x k f)). Qed.
Lemma lem4405505 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (f : K -> A) : (term191 A K s x k f) = (term199 A K s x k f).
Proof. exact (EQ_MP (@lem4405504 A K s x k f) (@lem4405496 A K s x k f)). Qed.
Lemma lem4405516 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (f : K -> A) : (term190 A K x s k f) = (term199 A K s x k f).
Proof. exact (TRANS (@lem4405492 A K s x k f) (@lem4405505 A K s x k f)). Qed.
Lemma lem4405517 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) : (term200 A K x s k) = (term201 A K s x k).
Proof. exact (fun_ext (fun f : K -> A => @lem4405516 A K s x k f)). Qed.
Lemma lem4405518 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4405519 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) : (term179 A K x s k) = (term202 A K s x k).
Proof. exact (MK_COMB (@lem4405518 A K) (@lem4405517 A K s x k)). Qed.
Lemma lem4405524 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) : (term81 A K x s k) = (term202 A K s x k).
Proof. exact (TRANS (@lem4405463 A K x s k) (@lem4405519 A K s x k)). Qed.
Lemma lem4405525 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) : (term203 A K x s k) = (term204 A K s x k).
Proof. exact (MK_COMB (@lem4405446 A K k x s) (@lem4405524 A K s x k)). Qed.
Lemma lem4405528 {A K : Type'} (x : K -> A) (s : type1470 A K) (k : K -> Prop) : (term204 A K s x k) = (term203 A K x s k).
Proof. exact (SYM (@lem4405525 A K s x k)). Qed.
Lemma lem4405529 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term142 A K k x s) : term142 A K k x s.
Proof. exact (h1). Qed.
Lemma lem4405530 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term28 A K k x s) : term28 A K k x s.
Proof. exact (h1). Qed.
Lemma lem4405531 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term125 A K k x.
Proof. exact (h1). Qed.
Lemma lem4405532 {A B : Type'} (s : A -> Prop) : term205 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4405533 {A B : Type'} (s : A -> Prop) : (term205 A B s) = (term206 A B s).
Proof. exact (eq_refl (term205 A B s)). Qed.
Lemma lem4405534 {A B : Type'} (s : A -> Prop) : term206 A B s.
Proof. exact (EQ_MP (@lem4405533 A B s) (@lem4405532 A B s)). Qed.
Lemma lem4405535 {A B : Type'} (s : A -> Prop) (f : A -> B) : term207 A B s f.
Proof. exact (@lem4405534 A B s f). Qed.
Lemma lem4405536 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term207 A B s f) = (term208 A B s f).
Proof. exact (eq_refl (term207 A B s f)). Qed.
Lemma lem4405537 {A B : Type'} (s : A -> Prop) (f : A -> B) : term208 A B s f.
Proof. exact (EQ_MP (@lem4405536 A B s f) (@lem4405535 A B s f)). Qed.
Lemma lem4405538 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term209 A B s f x.
Proof. exact (@lem4405537 A B s f x). Qed.
Lemma lem4405539 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term209 A B s f x) = ((@RESTRICTION A B s f x) = (term210 A B s f x)).
Proof. exact (eq_refl (term209 A B s f x)). Qed.
Lemma lem4405541 {A B : Type'} (f : A -> B) : term211 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4405542 {A B : Type'} (f : A -> B) : (term211 A B f) = (term212 A B f).
Proof. exact (eq_refl (term211 A B f)). Qed.
Lemma lem4405543 {A B : Type'} (f : A -> B) : term212 A B f.
Proof. exact (EQ_MP (@lem4405542 A B f) (@lem4405541 A B f)). Qed.
Lemma lem4405544 {A B : Type'} (f : A -> B) (g : A -> B) : term213 A B f g.
Proof. exact (@lem4405543 A B f g). Qed.
Lemma lem4405545 {A B : Type'} (f : A -> B) (g : A -> B) : (term213 A B f g) = ((f = g) = (term214 A B f g)).
Proof. exact (eq_refl (term213 A B f g)). Qed.
Lemma lem4405552 {A K : Type'} (i : K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term28 A K k x s) : term215 A K k x s i.
Proof. exact (@lem4405530 A K k x s h1 i). Qed.
Lemma lem4405553 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term215 A K k x s i) = (term216 A K k x s i).
Proof. exact (eq_refl (term215 A K k x s i)). Qed.
Lemma lem4405554 {A K : Type'} (i : K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term28 A K k x s) : term216 A K k x s i.
Proof. exact (EQ_MP (@lem4405553 A K k x s i) (@lem4405552 A K i k x s h1)). Qed.
Lemma lem4405555 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term216 A K k x s i) = ((term216 A K k x s i) = True).
Proof. exact (@lem7 (term216 A K k x s i)). Qed.
Lemma lem4405564 {A K : Type'} (i : K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term28 A K k x s) : (term216 A K k x s i) = True.
Proof. exact (EQ_MP (@lem4405555 A K k x s i) (@lem4405554 A K i k x s h1)). Qed.
Lemma lem4405565 {A K : Type'} (i : K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term28 A K k x s) : (term216 A K k x s i) = True.
Proof. exact (@lem4405564 A K i k x s h1). Qed.
Lemma lem4405566 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term28 A K k x s) : (term217 A K k x s) = (term218 K).
Proof. exact (fun_ext (fun i : K => @lem4405565 A K i k x s h1)). Qed.
Lemma lem4405567 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4405568 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term28 A K k x s) : (term28 A K k x s) = (term219 K).
Proof. exact (MK_COMB (@lem4405567 K) (@lem4405566 A K k x s h1)). Qed.
Lemma lem4405570 {A : Type'} (t : Prop) : (term116 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4405571 {K : Type'} (t : Prop) : (term116 K t) = t.
Proof. exact (@lem4405570 K t). Qed.
Lemma lem4405572 {K : Type'} : (term219 K) = True.
Proof. exact (@lem4405571 K True). Qed.
Lemma lem4405573 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term28 A K k x s) : (term28 A K k x s) = True.
Proof. exact (TRANS (@lem4405568 A K k x s h1) (@lem4405572 K)). Qed.
Lemma lem4405574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4405575 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term28 A K k x s) : (term220 A K k x s) = (and True).
Proof. exact (MK_COMB (@lem4405574) (@lem4405573 A K k x s h1)). Qed.
Lemma lem4405579 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term214 A B f g).
Proof. exact (EQ_MP (@lem4405545 A B f g) (@lem4405544 A B f g)). Qed.
Lemma lem4405580 {A K : Type'} (f : K -> A) (g : K -> A) : (f = g) = (term221 A K f g).
Proof. exact (@lem4405579 K A f g). Qed.
Lemma lem4405581 {A K : Type'} (k : K -> Prop) (x : K -> A) : (x = (@RESTRICTION K A k x)) = (term222 A K k x).
Proof. exact (@lem4405580 A K x (@RESTRICTION K A k x)). Qed.
Lemma lem4405591 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term210 A B s f x).
Proof. exact (EQ_MP (@lem4405539 A B s f x) (@lem4405538 A B s f x)). Qed.
Lemma lem4405592 {A K : Type'} (s : K -> Prop) (f : K -> A) (x : K) : (@RESTRICTION K A s f x) = (term223 A K s f x).
Proof. exact (@lem4405591 K A s f x). Qed.
Lemma lem4405593 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (@RESTRICTION K A k x x') = (term223 A K k x x').
Proof. exact (@lem4405592 A K k x x'). Qed.
Lemma lem4405594 {A K : Type'} (x : K -> A) (x' : K) : (term224 A K x x') = (term224 A K x x').
Proof. exact (eq_refl (term224 A K x x')). Qed.
Lemma lem4405595 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : ((x x') = (@RESTRICTION K A k x x')) = ((x x') = (term223 A K k x x')).
Proof. exact (MK_COMB (@lem4405594 A K x x') (@lem4405593 A K k x x')). Qed.
Lemma lem4405600 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term225 A K k x) = (term226 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4405595 A K k x x')). Qed.
Lemma lem4405601 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4405602 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term222 A K k x) = (term227 A K k x).
Proof. exact (MK_COMB (@lem4405601 K) (@lem4405600 A K k x)). Qed.
Lemma lem4405607 {A K : Type'} (k : K -> Prop) (x : K -> A) : (x = (@RESTRICTION K A k x)) = (term227 A K k x).
Proof. exact (TRANS (@lem4405581 A K k x) (@lem4405602 A K k x)). Qed.
Lemma lem4405608 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term28 A K k x s) : (term228 A K s k x) = (term229 A K k x).
Proof. exact (MK_COMB (@lem4405575 A K k x s h1) (@lem4405607 A K k x)). Qed.
Lemma lem4405610 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4405611 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term229 A K k x) = (term227 A K k x).
Proof. exact (@lem4405610 (term227 A K k x)). Qed.
Lemma lem4405620 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term28 A K k x s) : (term228 A K s k x) = (term227 A K k x).
Proof. exact (TRANS (@lem4405608 A K k x s h1) (@lem4405611 A K k x)). Qed.
Lemma lem4405621 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term28 A K k x s) : (term227 A K k x) = (term228 A K s k x).
Proof. exact (SYM (@lem4405620 A K k x s h1)). Qed.
Lemma lem4405623 (p : Prop) : p = (term230 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4405624 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term227 A K k x) = (term231 A K k x).
Proof. exact (@lem4405623 (term227 A K k x)). Qed.
Lemma lem4405625 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term231 A K k x) = (term227 A K k x).
Proof. exact (SYM (@lem4405624 A K k x)). Qed.
Lemma lem4405626 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term232 A K k x) : term232 A K k x.
Proof. exact (h1). Qed.
Lemma lem4405629 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term233 A K s k x) : term233 A K s k x.
Proof. exact (h1). Qed.
Lemma lem4405630 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : term234 A K s k x.
Proof. exact (fun h0 : term233 A K s k x => @lem4405629 A K s k x h0). Qed.
Lemma lem4405631 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term234 A K s k x) : term234 A K s k x.
Proof. exact (h1). Qed.
Lemma lem4405632 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term233 A K s k x) : term233 A K s k x.
Proof. exact (h1). Qed.
Lemma lem4405633 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term233 A K s k x) (h2 : term234 A K s k x) : term233 A K s k x.
Proof. exact (@lem4405631 A K s k x h2 (@lem4405632 A K s k x h1)). Qed.
Lemma lem4405634 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term233 A K s k x) : term235 A K s k x.
Proof. exact (fun h0 : term234 A K s k x => @lem4405633 A K s k x h1 h0). Qed.
Lemma lem4405635 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term234 A K s k x) : term234 A K s k x.
Proof. exact (h1). Qed.
Lemma lem4405636 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term233 A K s k x) (h2 : term234 A K s k x) : term233 A K s k x.
Proof. exact (@lem4405634 A K s k x h1 (@lem4405635 A K s k x h2)). Qed.
Lemma lem4405637 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term234 A K s k x) : term234 A K s k x.
Proof. exact (fun h0 : term233 A K s k x => @lem4405636 A K s k x h0 h1). Qed.
Lemma lem4405638 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : term236 A K s k x.
Proof. exact (fun h0 : term234 A K s k x => @lem4405637 A K s k x h0). Qed.
Lemma lem4405641 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : term234 A K s k x.
Proof. exact (@lem4405638 A K s k x (@lem4405630 A K s k x)). Qed.
Lemma lem4405642 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : term234 A K s k x.
Proof. exact (@lem4405641 A K s k x). Qed.
Lemma lem4405672 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4405673 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term231 A K k x) = (term237 A K k x).
Proof. exact (@lem4405672 (term232 A K k x)). Qed.
Lemma lem4405675 (t : Prop) : (term238 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4405676 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term237 A K k x) = (term227 A K k x).
Proof. exact (@lem4405675 (term227 A K k x)). Qed.
Lemma lem4405681 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term231 A K k x) = (term227 A K k x).
Proof. exact (TRANS (@lem4405673 A K k x) (@lem4405676 A K k x)). Qed.
Lemma lem4405682 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term93 A K k x s) = (term93 A K k x s).
Proof. exact (eq_refl (term93 A K k x s)). Qed.
Lemma lem4405683 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term239 A K s k x) = (term240 A K s k x).
Proof. exact (MK_COMB (@lem4405682 A K k x s) (@lem4405681 A K k x)). Qed.
Lemma lem4405686 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term241 A K k x) = (term241 A K k x).
Proof. exact (eq_refl (term241 A K k x)). Qed.
Lemma lem4405687 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term233 A K s k x) = (term242 A K s k x).
Proof. exact (MK_COMB (@lem4405686 A K k x) (@lem4405683 A K s k x)). Qed.
Lemma lem4405690 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term243 A K k x) = (term244 A K k x).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4405687 A K s k x)). Qed.
Lemma lem4405691 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4405692 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term245 A K k x) = (term246 A K k x).
Proof. exact (MK_COMB (@lem4405691 A K) (@lem4405690 A K k x)). Qed.
Lemma lem4405697 {A K : Type'} (x : K -> A) : (term247 A K x) = (term248 A K x).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4405692 A K k x)). Qed.
Lemma lem4405698 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4405699 {A K : Type'} (x : K -> A) : (term249 A K x) = (term250 A K x).
Proof. exact (MK_COMB (@lem4405698 K) (@lem4405697 A K x)). Qed.
Lemma lem4405704 {A K : Type'} : (term251 A K) = (term252 A K).
Proof. exact (fun_ext (fun x : K -> A => @lem4405699 A K x)). Qed.
Lemma lem4405705 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4405714 {A K : Type'} : (term253 A K) = (term254 A K).
Proof. exact (MK_COMB (@lem4405705 A K) (@lem4405704 A K)). Qed.
Lemma lem4405718 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (@IN K x k) = False.
Proof. exact (h1). Qed.
Lemma lem4405719 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4405720 {A K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = False) : (term255 A K x k) = (@COND A False).
Proof. exact (MK_COMB (@lem4405719 A) (@lem4405718 K x k h1)). Qed.
Lemma lem4405721 {A K : Type'} (x : K -> A) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4405722 {A K : Type'} (x : K -> A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = False) : (term256 A K k x x') = (term257 A K x x').
Proof. exact (MK_COMB (@lem4405720 A K x' k h1) (@lem4405721 A K x x')). Qed.
Lemma lem4405723 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4405724 {A K : Type'} (x : K -> A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = False) : (term223 A K k x x') = (term258 A K x x').
Proof. exact (MK_COMB (@lem4405722 A K x x' k h1) (@lem4405723 A)). Qed.
Lemma lem4405726 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4405727 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4405726 A t1 t2). Qed.
Lemma lem4405728 {A K : Type'} (x : K -> A) (x' : K) : (term258 A K x x') = (@ARB A).
Proof. exact (@lem4405727 A (x x') (@ARB A)). Qed.
Lemma lem4405729 {A K : Type'} (x : K -> A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = False) : (term223 A K k x x') = (@ARB A).
Proof. exact (TRANS (@lem4405724 A K x x' k h1) (@lem4405728 A K x x')). Qed.
Lemma lem4405730 {A K : Type'} (x : K -> A) (x' : K) : (term224 A K x x') = (term224 A K x x').
Proof. exact (eq_refl (term224 A K x x')). Qed.
Lemma lem4405731 {A K : Type'} (x : K -> A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = False) : ((x x') = (term223 A K k x x')) = ((x x') = (@ARB A)).
Proof. exact (MK_COMB (@lem4405730 A K x x') (@lem4405729 A K x x' k h1)). Qed.
Lemma lem4405734 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : term259 A K k x x'.
Proof. exact (fun h0 : (@IN K x' k) = False => @lem4405731 A K x x' k h0). Qed.
Lemma lem4405736 {K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (@IN K x k) = True.
Proof. exact (h1). Qed.
Lemma lem4405737 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4405738 {A K : Type'} (x : K) (k : K -> Prop) (h1 : (@IN K x k) = True) : (term255 A K x k) = (@COND A True).
Proof. exact (MK_COMB (@lem4405737 A) (@lem4405736 K x k h1)). Qed.
Lemma lem4405739 {A K : Type'} (x : K -> A) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4405740 {A K : Type'} (x : K -> A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = True) : (term256 A K k x x') = (term260 A K x x').
Proof. exact (MK_COMB (@lem4405738 A K x' k h1) (@lem4405739 A K x x')). Qed.
Lemma lem4405741 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4405742 {A K : Type'} (x : K -> A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = True) : (term223 A K k x x') = (term261 A K x x').
Proof. exact (MK_COMB (@lem4405740 A K x x' k h1) (@lem4405741 A)). Qed.
Lemma lem4405744 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4405745 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4405744 A t2 t1). Qed.
Lemma lem4405746 {A K : Type'} (x : K -> A) (x' : K) : (term261 A K x x') = (x x').
Proof. exact (@lem4405745 A (@ARB A) (x x')). Qed.
Lemma lem4405747 {A K : Type'} (x : K -> A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = True) : (term223 A K k x x') = (x x').
Proof. exact (TRANS (@lem4405742 A K x x' k h1) (@lem4405746 A K x x')). Qed.
Lemma lem4405748 {A K : Type'} (x : K -> A) (x' : K) : (term224 A K x x') = (term224 A K x x').
Proof. exact (eq_refl (term224 A K x x')). Qed.
Lemma lem4405749 {A K : Type'} (x : K -> A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = True) : ((x x') = (term223 A K k x x')) = ((x x') = (x x')).
Proof. exact (MK_COMB (@lem4405748 A K x x') (@lem4405747 A K x x' k h1)). Qed.
Lemma lem4405751 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4405752 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem4405751 A x). Qed.
Lemma lem4405753 {A K : Type'} (x : K -> A) (x' : K) : ((x x') = (x x')) = True.
Proof. exact (@lem4405752 A (x x')). Qed.
Lemma lem4405754 {A K : Type'} (x : K -> A) (x' : K) (k : K -> Prop) (h1 : (@IN K x' k) = True) : ((x x') = (term223 A K k x x')) = True.
Proof. exact (TRANS (@lem4405749 A K x x' k h1) (@lem4405753 A K x x')). Qed.
Lemma lem4405755 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : term262 A K k x x'.
Proof. exact (fun h0 : (@IN K x' k) = True => @lem4405754 A K x x' k h0). Qed.
Lemma lem4405756 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : term263 A K k x x'.
Proof. exact (conj (@lem4405734 A K k x x') (@lem4405755 A K k x x')). Qed.
Lemma lem4405758 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term264 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4405759 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : term265 A K k x x'.
Proof. exact (@lem4405758 ((x x') = (term223 A K k x x')) True (@IN K x' k) ((x x') = (@ARB A))). Qed.
Lemma lem4405760 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : ((x x') = (term223 A K k x x')) = (term266 A K k x x').
Proof. exact (@lem4405759 A K k x x' (@lem4405756 A K k x x')). Qed.
Lemma lem4405763 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term267 A K k x x') = (term267 A K k x x').
Proof. exact (eq_refl (term267 A K k x x')). Qed.
Lemma lem4405765 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4405766 {K : Type'} (x : K) (k : K -> Prop) : (term268 K x k) = True.
Proof. exact (@lem4405765 (term269 K x k)). Qed.
Lemma lem4405767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4405768 {K : Type'} (x : K) (k : K -> Prop) : (term270 K x k) = (and True).
Proof. exact (MK_COMB (@lem4405767) (@lem4405766 K x k)). Qed.
Lemma lem4405769 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term266 A K k x x') = (term271 A K k x x').
Proof. exact (MK_COMB (@lem4405768 K x' k) (@lem4405763 A K k x x')). Qed.
Lemma lem4405771 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4405772 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term271 A K k x x') = (term267 A K k x x').
Proof. exact (@lem4405771 (term267 A K k x x')). Qed.
Lemma lem4405773 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term266 A K k x x') = (term267 A K k x x').
Proof. exact (TRANS (@lem4405769 A K k x x') (@lem4405772 A K k x x')). Qed.
Lemma lem4405782 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : ((x x') = (term223 A K k x x')) = (term267 A K k x x').
Proof. exact (TRANS (@lem4405760 A K k x x') (@lem4405773 A K k x x')). Qed.
Lemma lem4405783 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term226 A K k x) = (term272 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4405782 A K k x x')). Qed.
Lemma lem4405784 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4405785 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term227 A K k x) = (term273 A K k x).
Proof. exact (MK_COMB (@lem4405784 K) (@lem4405783 A K k x)). Qed.
Lemma lem4405790 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term216 A K k x s i) = (term216 A K k x s i).
Proof. exact (eq_refl (term216 A K k x s i)). Qed.
Lemma lem4405791 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term217 A K k x s) = (term217 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4405790 A K k x s i)). Qed.
Lemma lem4405792 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4405793 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term28 A K k x s) = (term28 A K k x s).
Proof. exact (MK_COMB (@lem4405792 K) (@lem4405791 A K k x s)). Qed.
Lemma lem4405794 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4405795 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term93 A K k x s) = (term93 A K k x s).
Proof. exact (MK_COMB (@lem4405794) (@lem4405793 A K k x s)). Qed.
Lemma lem4405796 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term240 A K s k x) = (term274 A K s k x).
Proof. exact (MK_COMB (@lem4405795 A K k x s) (@lem4405785 A K k x)). Qed.
Lemma lem4405803 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term275 A K k x x') = (term275 A K k x x').
Proof. exact (eq_refl (term275 A K k x x')). Qed.
Lemma lem4405804 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term276 A K k x) = (term276 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4405803 A K k x x')). Qed.
Lemma lem4405805 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4405806 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term125 A K k x) = (term125 A K k x).
Proof. exact (MK_COMB (@lem4405805 K) (@lem4405804 A K k x)). Qed.
Lemma lem4405807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4405808 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term241 A K k x) = (term241 A K k x).
Proof. exact (MK_COMB (@lem4405807) (@lem4405806 A K k x)). Qed.
Lemma lem4405809 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term242 A K s k x) = (term277 A K s k x).
Proof. exact (MK_COMB (@lem4405808 A K k x) (@lem4405796 A K s k x)). Qed.
Lemma lem4405810 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term244 A K k x) = (term278 A K k x).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4405809 A K s k x)). Qed.
Lemma lem4405811 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4405812 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term246 A K k x) = (term279 A K k x).
Proof. exact (MK_COMB (@lem4405811 A K) (@lem4405810 A K k x)). Qed.
Lemma lem4405813 {A K : Type'} (x : K -> A) : (term248 A K x) = (term280 A K x).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4405812 A K k x)). Qed.
Lemma lem4405814 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4405815 {A K : Type'} (x : K -> A) : (term250 A K x) = (term281 A K x).
Proof. exact (MK_COMB (@lem4405814 K) (@lem4405813 A K x)). Qed.
Lemma lem4405816 {A K : Type'} : (term252 A K) = (term282 A K).
Proof. exact (fun_ext (fun x : K -> A => @lem4405815 A K x)). Qed.
Lemma lem4405817 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4405818 {A K : Type'} : (term254 A K) = (term283 A K).
Proof. exact (MK_COMB (@lem4405817 A K) (@lem4405816 A K)). Qed.
Lemma lem4405867 {A K : Type'} : (term253 A K) = (term283 A K).
Proof. exact (TRANS (@lem4405714 A K) (@lem4405818 A K)). Qed.
Lemma lem4405868 {A K : Type'} : (term283 A K) = (term253 A K).
Proof. exact (SYM (@lem4405867 A K)). Qed.
Lemma lem4405869 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term125 A K k x.
Proof. exact (h1). Qed.
Lemma lem4405872 (p : Prop) : p = (term230 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4405873 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term267 A K k x x') = (term284 A K k x x').
Proof. exact (@lem4405872 (term267 A K k x x')). Qed.
Lemma lem4405874 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term284 A K k x x') = (term267 A K k x x').
Proof. exact (SYM (@lem4405873 A K k x x')). Qed.
Lemma lem4405875 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term285 A K k x x') : term285 A K k x x'.
Proof. exact (h1). Qed.
Lemma lem4405878 {K : Type'} (x : K) (k : K -> Prop) : (term286 K x k) = (@IN K x k).
Proof. exact (@lem16933 (@IN K x k)). Qed.
Lemma lem4405879 {A K : Type'} (x : K -> A) (x' : K) : ((x x') = (@ARB A)) = ((x x') = (@ARB A)).
Proof. exact (eq_refl ((x x') = (@ARB A))). Qed.
Lemma lem4405880 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4405881 {K : Type'} (x : K) (k : K -> Prop) : (term287 K x k) = (term288 K x k).
Proof. exact (MK_COMB (@lem4405880) (@lem4405878 K x k)). Qed.
Lemma lem4405882 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term289 A K k x x') = (term267 A K k x x').
Proof. exact (MK_COMB (@lem4405881 K x' k) (@lem4405879 A K x x')). Qed.
Lemma lem4405883 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term275 A K k x x') = (term289 A K k x x').
Proof. exact (@lem17265 (term269 K x' k) ((x x') = (@ARB A))). Qed.
Lemma lem4405884 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term275 A K k x x') = (term267 A K k x x').
Proof. exact (TRANS (@lem4405883 A K k x x') (@lem4405882 A K k x x')). Qed.
Lemma lem4405885 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term276 A K k x) = (term272 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4405884 A K k x x')). Qed.
Lemma lem4405886 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4405939 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term125 A K k x) = (term273 A K k x).
Proof. exact (MK_COMB (@lem4405886 K) (@lem4405885 A K k x)). Qed.
Lemma lem4405940 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term273 A K k x.
Proof. exact (EQ_MP (@lem4405939 A K k x) (@lem4405869 A K k x h1)). Qed.
Lemma lem4406014 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term285 A K k x x') = (term290 A K k x x').
Proof. exact (@lem17160 (@IN K x' k) ((x x') = (@ARB A))). Qed.
Lemma lem4406030 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term267 A K k x x') = (term267 A K k x x').
Proof. exact (eq_refl (term267 A K k x x')). Qed.
Lemma lem4406031 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term272 A K k x) = (term272 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4406030 A K k x x')). Qed.
Lemma lem4406032 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4406033 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term273 A K k x) = (term273 A K k x).
Proof. exact (MK_COMB (@lem4406032 K) (@lem4406031 A K k x)). Qed.
Lemma lem4406034 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term273 A K k x.
Proof. exact (EQ_MP (@lem4406033 A K k x) (@lem4405940 A K k x h1)). Qed.
Lemma lem4406077 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term285 A K k x x') : term290 A K k x x'.
Proof. exact (EQ_MP (@lem4406014 A K k x x') (@lem4405875 A K k x x' h1)). Qed.
Lemma lem4406087 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term267 A K k x x') = (term267 A K k x x').
Proof. exact (eq_refl (term267 A K k x x')). Qed.
Lemma lem4406088 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term272 A K k x) = (term272 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4406087 A K k x x')). Qed.
Lemma lem4406089 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4406091 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term273 A K k x) = (term273 A K k x).
Proof. exact (MK_COMB (@lem4406089 K) (@lem4406088 A K k x)). Qed.
Lemma lem4406092 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term273 A K k x.
Proof. exact (EQ_MP (@lem4406091 A K k x) (@lem4406034 A K k x h1)). Qed.
Lemma lem4406114 {A K : Type'} (_50431 : K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term291 A K k x _50431.
Proof. exact (@lem4406092 A K k x h1 _50431). Qed.
Lemma lem4406115 {A K : Type'} (k : K -> Prop) (x : K -> A) (_50431 : K) : (term291 A K k x _50431) = (term267 A K k x _50431).
Proof. exact (eq_refl (term291 A K k x _50431)). Qed.
Lemma lem4406125 {A K : Type'} (_50431 : K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term267 A K k x _50431.
Proof. exact (EQ_MP (@lem4406115 A K k x _50431) (@lem4406114 A K _50431 k x h1)). Qed.
Lemma lem4406135 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term285 A K k x x') : term292 A K x x'.
Proof. exact (proj2 (@lem4406077 A K k x x' h1)). Qed.
Lemma lem4406199 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term285 A K k x x') : term269 K x' k.
Proof. exact (proj1 (@lem4406077 A K k x x' h1)). Qed.
Lemma lem4406200 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term285 A K k x x') : term293 K x' k.
Proof. exact (fun h0 : @IN K x' k => @lem4406199 A K k x x' h1). Qed.
Lemma lem4406202 (p : Prop) : (term294 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4406203 {K : Type'} (x' : K) (k : K -> Prop) : (term293 K x' k) = (term269 K x' k).
Proof. exact (@lem4406202 (@IN K x' k)). Qed.
Lemma lem4406204 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term285 A K k x x') : term269 K x' k.
Proof. exact (EQ_MP (@lem4406203 K x' k) (@lem4406200 A K k x x' h1)). Qed.
Lemma lem4406210 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4406211 {A K : Type'} (x : K -> A) (_50431 : K) (k : K -> Prop) : (term267 A K k x _50431) = (term295 A K x _50431 k).
Proof. exact (@lem4406210 ((x _50431) = (@ARB A)) (@IN K _50431 k)). Qed.
Lemma lem4406219 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4406220 {A K : Type'} (x : K -> A) (_50431 : K) (k : K -> Prop) : (term296 A K k x _50431) = (term297 A K x _50431 k).
Proof. exact (MK_COMB (@lem4406219) (@lem4406211 A K x _50431 k)). Qed.
Lemma lem4406228 {A K : Type'} (x : K -> A) (_50431 : K) (k : K -> Prop) : (term295 A K x _50431 k) = (term295 A K x _50431 k).
Proof. exact (eq_refl (term295 A K x _50431 k)). Qed.
Lemma lem4406229 {A K : Type'} (x : K -> A) (_50431 : K) (k : K -> Prop) : ((term267 A K k x _50431) = (term295 A K x _50431 k)) = ((term295 A K x _50431 k) = (term295 A K x _50431 k)).
Proof. exact (MK_COMB (@lem4406220 A K x _50431 k) (@lem4406228 A K x _50431 k)). Qed.
Lemma lem4406231 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4406232 (x : Prop) : (x = x) = True.
Proof. exact (@lem4406231 Prop x). Qed.
Lemma lem4406233 {A K : Type'} (x : K -> A) (_50431 : K) (k : K -> Prop) : ((term295 A K x _50431 k) = (term295 A K x _50431 k)) = True.
Proof. exact (@lem4406232 (term295 A K x _50431 k)). Qed.
Lemma lem4406234 {A K : Type'} (x : K -> A) (_50431 : K) (k : K -> Prop) : ((term267 A K k x _50431) = (term295 A K x _50431 k)) = True.
Proof. exact (TRANS (@lem4406229 A K x _50431 k) (@lem4406233 A K x _50431 k)). Qed.
Lemma lem4406235 {A K : Type'} (x : K -> A) (_50431 : K) (k : K -> Prop) : True = ((term267 A K k x _50431) = (term295 A K x _50431 k)).
Proof. exact (SYM (@lem4406234 A K x _50431 k)). Qed.
Lemma lem4406236 {A K : Type'} (x : K -> A) (_50431 : K) (k : K -> Prop) : (term267 A K k x _50431) = (term295 A K x _50431 k).
Proof. exact (EQ_MP (@lem4406235 A K x _50431 k) (@lem0)). Qed.
Lemma lem4406237 {A K : Type'} (_50431 : K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term295 A K x _50431 k.
Proof. exact (EQ_MP (@lem4406236 A K x _50431 k) (@lem4406125 A K _50431 k x h1)). Qed.
Lemma lem4406239 (b : Prop) (a : Prop) : (a \/ b) = (term298 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4406242 {A K : Type'} (k : K -> Prop) (x : K -> A) (_50431 : K) : (term295 A K x _50431 k) = (term275 A K k x _50431).
Proof. exact (@lem4406239 (@IN K _50431 k) ((x _50431) = (@ARB A))). Qed.
Lemma lem4406245 {A K : Type'} (_50431 : K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term275 A K k x _50431.
Proof. exact (EQ_MP (@lem4406242 A K k x _50431) (@lem4406237 A K _50431 k x h1)). Qed.
Lemma lem4406246 {A K : Type'} (_50431 : K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term275 A K k x _50431.
Proof. exact (@lem4406245 A K _50431 k x h1). Qed.
Lemma lem4406247 {A K : Type'} (x' : K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term275 A K k x x'.
Proof. exact (@lem4406246 A K x' k x h1). Qed.
Lemma lem4406250 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term125 A K k x) (h2 : term285 A K k x x') : (x x') = (@ARB A).
Proof. exact (@lem4406247 A K x' k x h1 (@lem4406204 A K k x x' h2)). Qed.
Lemma lem4406251 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term125 A K k x) (h2 : term285 A K k x x') : term299 A K x x'.
Proof. exact (fun h0 : term292 A K x x' => @lem4406250 A K k x x' h1 h2). Qed.
Lemma lem4406253 (p : Prop) : (term300 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4406254 {A K : Type'} (x : K -> A) (x' : K) : (term299 A K x x') = ((x x') = (@ARB A)).
Proof. exact (@lem4406253 ((x x') = (@ARB A))). Qed.
Lemma lem4406255 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term125 A K k x) (h2 : term285 A K k x x') : (x x') = (@ARB A).
Proof. exact (EQ_MP (@lem4406254 A K x x') (@lem4406251 A K k x x' h1 h2)). Qed.
Lemma lem4406258 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4406260 {A K : Type'} (x : K -> A) (x' : K) : (term292 A K x x') = (term301 A K x x').
Proof. exact (@lem4406258 ((x x') = (@ARB A))). Qed.
Lemma lem4406263 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term285 A K k x x') : term301 A K x x'.
Proof. exact (EQ_MP (@lem4406260 A K x x') (@lem4406135 A K k x x' h1)). Qed.
Lemma lem4406266 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term125 A K k x) (h2 : term285 A K k x x') : False.
Proof. exact (@lem4406263 A K k x x' h2 (@lem4406255 A K k x x' h1 h2)). Qed.
Lemma lem4406267 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term125 A K k x) (h2 : term285 A K k x x') : term302.
Proof. exact (fun h0 : ~ False => @lem4406266 A K k x x' h1 h2). Qed.
Lemma lem4406269 (p : Prop) : (term300 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4406270 : term302 = False.
Proof. exact (@lem4406269 False). Qed.
Lemma lem4406271 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term125 A K k x) (h2 : term285 A K k x x') : False.
Proof. exact (EQ_MP (@lem4406270) (@lem4406267 A K k x x' h1 h2)). Qed.
Lemma lem4406272 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term125 A K k x) (h2 : term285 A K k x x') : (term285 A K k x x') = False.
Proof. exact (prop_ext (fun h3 : term285 A K k x x' => @lem4406271 A K k x x' h1 h2) (fun h3 : False => @lem4405875 A K k x x' h2)). Qed.
Lemma lem4406273 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (h1 : term125 A K k x) (h2 : term285 A K k x x') : False.
Proof. exact (EQ_MP (@lem4406272 A K k x x' h1 h2) (@lem4405875 A K k x x' h2)). Qed.
Lemma lem4406274 {A K : Type'} (x' : K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term284 A K k x x'.
Proof. exact (fun h0 : term285 A K k x x' => @lem4406273 A K k x x' h1 h0). Qed.
Lemma lem4406275 {A K : Type'} (x' : K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term267 A K k x x'.
Proof. exact (EQ_MP (@lem4405874 A K k x x') (@lem4406274 A K x' k x h1)). Qed.
Lemma lem4406280 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term273 A K k x.
Proof. exact (fun x' : K => @lem4406275 A K x' k x h1). Qed.
Lemma lem4406281 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term274 A K s k x.
Proof. exact (fun h0 : term28 A K k x s => @lem4406280 A K k x h1). Qed.
Lemma lem4406282 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : term277 A K s k x.
Proof. exact (fun h0 : term125 A K k x => @lem4406281 A K s k x h0). Qed.
Lemma lem4406287 {A K : Type'} (k : K -> Prop) (x : K -> A) : term279 A K k x.
Proof. exact (fun s : type1470 A K => @lem4406282 A K s k x). Qed.
Lemma lem4406292 {A K : Type'} (x : K -> A) : term281 A K x.
Proof. exact (fun k : K -> Prop => @lem4406287 A K k x). Qed.
Lemma lem4406297 {A K : Type'} : term283 A K.
Proof. exact (fun x : K -> A => @lem4406292 A K x). Qed.
Lemma lem4406298 {A K : Type'} : term253 A K.
Proof. exact (EQ_MP (@lem4405868 A K) (@lem4406297 A K)). Qed.
Lemma lem4406299 {A K : Type'} (x : K -> A) : term303 A K x.
Proof. exact (@lem4406298 A K x). Qed.
Lemma lem4406300 {A K : Type'} (x : K -> A) : (term303 A K x) = (term249 A K x).
Proof. exact (eq_refl (term303 A K x)). Qed.
Lemma lem4406301 {A K : Type'} (x : K -> A) : term249 A K x.
Proof. exact (EQ_MP (@lem4406300 A K x) (@lem4406299 A K x)). Qed.
Lemma lem4406302 {A K : Type'} (x : K -> A) (k : K -> Prop) : term304 A K x k.
Proof. exact (@lem4406301 A K x k). Qed.
Lemma lem4406303 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term304 A K x k) = (term245 A K k x).
Proof. exact (eq_refl (term304 A K x k)). Qed.
Lemma lem4406304 {A K : Type'} (k : K -> Prop) (x : K -> A) : term245 A K k x.
Proof. exact (EQ_MP (@lem4406303 A K k x) (@lem4406302 A K x k)). Qed.
Lemma lem4406305 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : term305 A K k x s.
Proof. exact (@lem4406304 A K k x s). Qed.
Lemma lem4406306 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term305 A K k x s) = (term233 A K s k x).
Proof. exact (eq_refl (term305 A K k x s)). Qed.
Lemma lem4406307 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : term233 A K s k x.
Proof. exact (EQ_MP (@lem4406306 A K s k x) (@lem4406305 A K k x s)). Qed.
Lemma lem4406309 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : term233 A K s k x.
Proof. exact (@lem4405642 A K s k x (@lem4406307 A K s k x)). Qed.
Lemma lem4406310 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) : term239 A K s k x.
Proof. exact (@lem4406309 A K s k x (@lem4405531 A K k x h1)). Qed.
Lemma lem4406311 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term125 A K k x) (h2 : term28 A K k x s) : term231 A K k x.
Proof. exact (@lem4406310 A K s k x h1 (@lem4405530 A K k x s h2)). Qed.
Lemma lem4406312 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) (h2 : term28 A K k x s) (h3 : term232 A K k x) : False.
Proof. exact (@lem4406311 A K k x s h1 h2 (@lem4405626 A K k x h3)). Qed.
Lemma lem4406313 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) (h2 : term28 A K k x s) (h3 : term232 A K k x) : (term232 A K k x) = False.
Proof. exact (prop_ext (fun h4 : term232 A K k x => @lem4406312 A K s k x h1 h2 h3) (fun h4 : False => @lem4405626 A K k x h3)). Qed.
Lemma lem4406314 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term125 A K k x) (h2 : term28 A K k x s) (h3 : term232 A K k x) : False.
Proof. exact (EQ_MP (@lem4406313 A K s k x h1 h2 h3) (@lem4405626 A K k x h3)). Qed.
Lemma lem4406315 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term125 A K k x) (h2 : term28 A K k x s) : term231 A K k x.
Proof. exact (fun h0 : term232 A K k x => @lem4406314 A K s k x h1 h2 h0). Qed.
Lemma lem4406316 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term125 A K k x) (h2 : term28 A K k x s) : term227 A K k x.
Proof. exact (EQ_MP (@lem4405625 A K k x) (@lem4406315 A K k x s h1 h2)). Qed.
Lemma lem4406317 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term125 A K k x) (h2 : term28 A K k x s) : term228 A K s k x.
Proof. exact (EQ_MP (@lem4405621 A K k x s h2) (@lem4406316 A K k x s h1 h2)). Qed.
Lemma lem4406318 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term125 A K k x) (h2 : term28 A K k x s) : term202 A K s x k.
Proof. exact (ex_intro (term201 A K s x k) x (@lem4406317 A K k x s h1 h2)). Qed.
Lemma lem4406319 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term142 A K k x s) : term28 A K k x s.
Proof. exact (proj2 (@lem4405529 A K k x s h1)). Qed.
Lemma lem4406320 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term142 A K k x s) : term125 A K k x.
Proof. exact (proj1 (@lem4405529 A K k x s h1)). Qed.
Lemma lem4406321 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term125 A K k x) (h2 : term28 A K k x s) : (term28 A K k x s) = (term202 A K s x k).
Proof. exact (prop_ext (fun h3 : term28 A K k x s => @lem4406318 A K k x s h1 h2) (fun h3 : term202 A K s x k => @lem4405530 A K k x s h2)). Qed.
Lemma lem4406322 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term125 A K k x) (h2 : term28 A K k x s) : term202 A K s x k.
Proof. exact (EQ_MP (@lem4406321 A K k x s h1 h2) (@lem4405530 A K k x s h2)). Qed.
Lemma lem4406323 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term125 A K k x) (h2 : term28 A K k x s) : (term125 A K k x) = (term202 A K s x k).
Proof. exact (prop_ext (fun h3 : term125 A K k x => @lem4406322 A K k x s h1 h2) (fun h3 : term202 A K s x k => @lem4405531 A K k x h1)). Qed.
Lemma lem4406324 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term125 A K k x) (h2 : term28 A K k x s) : term202 A K s x k.
Proof. exact (EQ_MP (@lem4406323 A K k x s h1 h2) (@lem4405531 A K k x h1)). Qed.
Lemma lem4406325 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term125 A K k x) (h2 : term142 A K k x s) : (term28 A K k x s) = (term202 A K s x k).
Proof. exact (prop_ext (fun h3 : term28 A K k x s => @lem4406324 A K k x s h1 h3) (fun h3 : term202 A K s x k => @lem4406319 A K k x s h2)). Qed.
Lemma lem4406326 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term125 A K k x) (h2 : term142 A K k x s) : term202 A K s x k.
Proof. exact (EQ_MP (@lem4406325 A K k x s h1 h2) (@lem4406319 A K k x s h2)). Qed.
Lemma lem4406327 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term142 A K k x s) : (term125 A K k x) = (term202 A K s x k).
Proof. exact (prop_ext (fun h2 : term125 A K k x => @lem4406326 A K k x s h2 h1) (fun h2 : term202 A K s x k => @lem4406320 A K k x s h1)). Qed.
Lemma lem4406328 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term142 A K k x s) : term202 A K s x k.
Proof. exact (EQ_MP (@lem4406327 A K k x s h1) (@lem4406320 A K k x s h1)). Qed.
Lemma lem4406329 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) : term204 A K s x k.
Proof. exact (fun h0 : term142 A K k x s => @lem4406328 A K k x s h0). Qed.
Lemma lem4406330 {A K : Type'} (x : K -> A) (s : type1470 A K) (k : K -> Prop) : term203 A K x s k.
Proof. exact (EQ_MP (@lem4405528 A K x s k) (@lem4406329 A K s x k)). Qed.
Lemma lem4406335 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : term55 A K s k.
Proof. exact (fun x : K -> A => @lem4406330 A K x s k). Qed.
Lemma lem4406336 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term112 A K k s.
Proof. exact (EQ_MP (@lem4405316 A K k s) (@lem4406335 A K s k)). Qed.
Lemma lem4406337 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (@cartesian_product A K k s) = (term51 A K s k).
Proof. exact (EQ_MP (@lem4405240 A K s k) (@lem4406336 A K k s)). Qed.
Lemma lem4406342 {A K : Type'} (k : K -> Prop) : term306 A K k.
Proof. exact (fun s : type1470 A K => @lem4406337 A K s k). Qed.
Lemma lem4406347 {A K : Type'} : term307 A K.
Proof. exact (fun k : K -> Prop => @lem4406342 A K k). Qed.

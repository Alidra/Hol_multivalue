Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_IMAGE_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EQ_TRANS_spec.
Require Import FINITE_IMAGE_spec.
Require Import ITERATE_EQ_spec.
Require Import ITERATE_RESTRICT_SET_spec.
Require Import ITERATE_SING_spec.
Require Import ITERATE_SWAP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1834_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem6155070 {A B : Type'} (op : type1400 B) : term0 A B op.
Proof. exact (@lem5985778 A B op). Qed.
Lemma lem6155071 {A B : Type'} (op : type1400 B) : (term0 A B op) = (term1 A B op).
Proof. exact (eq_refl (term0 A B op)). Qed.
Lemma lem6155073 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem6155074 {A : Type'} (x : A) (h1 : term2 A) : term3 A x.
Proof. exact (@lem6155073 A h1 x). Qed.
Lemma lem6155075 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem6155076 {A : Type'} (x : A) (h1 : term2 A) : term4 A x.
Proof. exact (EQ_MP (@lem6155075 A x) (@lem6155074 A x h1)). Qed.
Lemma lem6155077 {A : Type'} (x : A) (y : A) (h1 : term2 A) : term5 A x y.
Proof. exact (@lem6155076 A x h1 y). Qed.
Lemma lem6155078 {A : Type'} (y : A) (x : A) : (term5 A x y) = (term6 A y x).
Proof. exact (eq_refl (term5 A x y)). Qed.
Lemma lem6155079 {A : Type'} (y : A) (x : A) (h1 : term2 A) : term6 A y x.
Proof. exact (EQ_MP (@lem6155078 A y x) (@lem6155077 A x y h1)). Qed.
Lemma lem6155080 {A : Type'} (y : A) (x : A) (z : A) (h1 : term2 A) : term7 A y x z.
Proof. exact (@lem6155079 A y x h1 z). Qed.
Lemma lem6155081 {A : Type'} (y : A) (x : A) (z : A) : (term7 A y x z) = (term8 A y x z).
Proof. exact (eq_refl (term7 A y x z)). Qed.
Lemma lem6155082 {A : Type'} (y : A) (x : A) (z : A) (h1 : term2 A) : term8 A y x z.
Proof. exact (EQ_MP (@lem6155081 A y x z) (@lem6155080 A y x z h1)). Qed.
Lemma lem6155083 {A : Type'} (x : A) (y : A) (z : A) (h1 : term9 A x y z) : term9 A x y z.
Proof. exact (h1). Qed.
Lemma lem6155084 {A : Type'} (x : A) (y : A) (z : A) (h1 : term2 A) (h2 : term9 A x y z) : x = z.
Proof. exact (@lem6155082 A y x z h1 (@lem6155083 A x y z h2)). Qed.
Lemma lem6155085 {A : Type'} (x : A) (y : A) (z : A) (h1 : term9 A x y z) : term10 A x z.
Proof. exact (fun h0 : term2 A => @lem6155084 A x y z h0 h1). Qed.
Lemma lem6155086 {A : Type'} (x : A) (z : A) (h1 : term11 A x z) : term11 A x z.
Proof. exact (h1). Qed.
Lemma lem6155087 {A : Type'} (x : A) (z : A) (h1 : term11 A x z) : term10 A x z.
Proof. exact (ex_elim (@lem6155086 A x z h1) (fun y : A => fun h0 : term12 A x z y => @lem6155085 A x y z h0)). Qed.
Lemma lem6155088 {A : Type'} (h1 : term2 A) : term2 A.
Proof. exact (h1). Qed.
Lemma lem6155089 {A : Type'} (x : A) (z : A) (h1 : term2 A) (h2 : term11 A x z) : x = z.
Proof. exact (@lem6155087 A x z h2 (@lem6155088 A h1)). Qed.
Lemma lem6155090 {A : Type'} (x : A) (z : A) (h1 : term2 A) : term13 A x z.
Proof. exact (fun h0 : term11 A x z => @lem6155089 A x z h1 h0). Qed.
Lemma lem6155091 {A : Type'} (x : A) (h1 : term2 A) : term14 A x.
Proof. exact (fun z : A => @lem6155090 A x z h1). Qed.
Lemma lem6155092 {A : Type'} (h1 : term2 A) : term15 A.
Proof. exact (fun x : A => @lem6155091 A x h1). Qed.
Lemma lem6155093 {A : Type'} : term16 A.
Proof. exact (fun h0 : term2 A => @lem6155092 A h0). Qed.
Lemma lem6155094 {A : Type'} : term15 A.
Proof. exact (@lem6155093 A (@lem403 A)). Qed.
Lemma lem6155095 {A : Type'} (x : A) : term17 A x.
Proof. exact (@lem6155094 A x). Qed.
Lemma lem6155096 {A : Type'} (x : A) : (term17 A x) = (term14 A x).
Proof. exact (eq_refl (term17 A x)). Qed.
Lemma lem6155097 {A : Type'} (x : A) : term14 A x.
Proof. exact (EQ_MP (@lem6155096 A x) (@lem6155095 A x)). Qed.
Lemma lem6155098 {A : Type'} (x : A) (z : A) : term18 A x z.
Proof. exact (@lem6155097 A x z). Qed.
Lemma lem6155099 {A : Type'} (x : A) (z : A) : (term18 A x z) = (term13 A x z).
Proof. exact (eq_refl (term18 A x z)). Qed.
Lemma lem6155101 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem6155102 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6155104 {A : Type'} (x : A) (z : A) : term13 A x z.
Proof. exact (EQ_MP (@lem6155099 A x z) (@lem6155098 A x z)). Qed.
Lemma lem6155105 {C : Type'} (x : C) (z : C) : term13 C x z.
Proof. exact (@lem6155104 C x z). Qed.
Lemma lem6155106 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) : term19 A B C op s f g.
Proof. exact (@lem6155105 C (@iterate C A op s g) (term20 A B C op s f g)). Qed.
Lemma lem6155110 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (EQ_MP (@lem6155071 A B op) (@lem6155070 A B op)). Qed.
Lemma lem6155111 {A C : Type'} (op : type1400 C) : term1 A C op.
Proof. exact (@lem6155110 A C op). Qed.
Lemma lem6155112 {A C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term21 A C op.
Proof. exact (@lem6155111 A C op (@lem6155101 C op h1)). Qed.
Lemma lem6155113 {A C : Type'} (op : type1400 C) (h1 : term21 A C op) : term21 A C op.
Proof. exact (h1). Qed.
Lemma lem6155114 {A C : Type'} (f : A -> C) (op : type1400 C) (h1 : term21 A C op) : term22 A C op f.
Proof. exact (@lem6155113 A C op h1 f). Qed.
Lemma lem6155115 {A C : Type'} (f : A -> C) (op : type1400 C) : (term22 A C op f) = (term23 A C f op).
Proof. exact (eq_refl (term22 A C op f)). Qed.
Lemma lem6155116 {A C : Type'} (f : A -> C) (op : type1400 C) (h1 : term21 A C op) : term23 A C f op.
Proof. exact (EQ_MP (@lem6155115 A C f op) (@lem6155114 A C f op h1)). Qed.
Lemma lem6155117 {A C : Type'} (f : A -> C) (g : A -> C) (op : type1400 C) (h1 : term21 A C op) : term24 A C f op g.
Proof. exact (@lem6155116 A C f op h1 g). Qed.
Lemma lem6155118 {A C : Type'} (f : A -> C) (op : type1400 C) (g : A -> C) : (term24 A C f op g) = (term25 A C f op g).
Proof. exact (eq_refl (term24 A C f op g)). Qed.
Lemma lem6155119 {A C : Type'} (f : A -> C) (g : A -> C) (op : type1400 C) (h1 : term21 A C op) : term25 A C f op g.
Proof. exact (EQ_MP (@lem6155118 A C f op g) (@lem6155117 A C f g op h1)). Qed.
Lemma lem6155120 {A C : Type'} (f : A -> C) (g : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : term21 A C op) : term26 A C f op g s.
Proof. exact (@lem6155119 A C f g op h1 s). Qed.
Lemma lem6155121 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term26 A C f op g s) = (term27 A C f op s g).
Proof. exact (eq_refl (term26 A C f op g s)). Qed.
Lemma lem6155122 {A C : Type'} (f : A -> C) (s : A -> Prop) (g : A -> C) (op : type1400 C) (h1 : term21 A C op) : term27 A C f op s g.
Proof. exact (EQ_MP (@lem6155121 A C f op s g) (@lem6155120 A C f g s op h1)). Qed.
Lemma lem6155123 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) (h1 : term28 A C s f g) : term28 A C s f g.
Proof. exact (h1). Qed.
Lemma lem6155124 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) (op : type1400 C) (h1 : term28 A C s f g) (h2 : term21 A C op) : (@iterate C A op s f) = (@iterate C A op s g).
Proof. exact (@lem6155122 A C f s g op h2 (@lem6155123 A C s f g h1)). Qed.
Lemma lem6155125 {A C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> C) (g : A -> C) (h1 : term28 A C s f g) : term29 A C f op s g.
Proof. exact (fun h0 : term21 A C op => @lem6155124 A C s f g op h1 h0). Qed.
Lemma lem6155126 {A C : Type'} (op : type1400 C) (h1 : term21 A C op) : term21 A C op.
Proof. exact (h1). Qed.
Lemma lem6155127 {A C : Type'} (s : A -> Prop) (f : A -> C) (g : A -> C) (op : type1400 C) (h1 : term28 A C s f g) (h2 : term21 A C op) : (@iterate C A op s f) = (@iterate C A op s g).
Proof. exact (@lem6155125 A C op s f g h1 (@lem6155126 A C op h2)). Qed.
Lemma lem6155128 {A C : Type'} (f : A -> C) (s : A -> Prop) (g : A -> C) (op : type1400 C) (h1 : term21 A C op) : term27 A C f op s g.
Proof. exact (fun h0 : term28 A C s f g => @lem6155127 A C s f g op h0 h1). Qed.
Lemma lem6155129 {A C : Type'} (f : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : term21 A C op) : term30 A C f op s.
Proof. exact (fun g : A -> C => @lem6155128 A C f s g op h1). Qed.
Lemma lem6155130 {A C : Type'} (f : A -> C) (op : type1400 C) (h1 : term21 A C op) : term31 A C f op.
Proof. exact (fun s : A -> Prop => @lem6155129 A C f s op h1). Qed.
Lemma lem6155131 {A C : Type'} (op : type1400 C) (h1 : term21 A C op) : term32 A C op.
Proof. exact (fun f : A -> C => @lem6155130 A C f op h1). Qed.
Lemma lem6155132 {A C : Type'} (op : type1400 C) : term33 A C op.
Proof. exact (fun h0 : term21 A C op => @lem6155131 A C op h0). Qed.
Lemma lem6155133 {A C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term32 A C op.
Proof. exact (@lem6155132 A C op (@lem6155112 A C op h1)). Qed.
Lemma lem6155134 {A C : Type'} (f : A -> C) (op : type1400 C) (h1 : @monoidal C op) : term34 A C op f.
Proof. exact (@lem6155133 A C op h1 f). Qed.
Lemma lem6155135 {A C : Type'} (f : A -> C) (op : type1400 C) : (term34 A C op f) = (term31 A C f op).
Proof. exact (eq_refl (term34 A C op f)). Qed.
Lemma lem6155136 {A C : Type'} (f : A -> C) (op : type1400 C) (h1 : @monoidal C op) : term31 A C f op.
Proof. exact (EQ_MP (@lem6155135 A C f op) (@lem6155134 A C f op h1)). Qed.
Lemma lem6155137 {A C : Type'} (f : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term35 A C f op s.
Proof. exact (@lem6155136 A C f op h1 s). Qed.
Lemma lem6155138 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) : (term35 A C f op s) = (term30 A C f op s).
Proof. exact (eq_refl (term35 A C f op s)). Qed.
Lemma lem6155139 {A C : Type'} (f : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term30 A C f op s.
Proof. exact (EQ_MP (@lem6155138 A C f op s) (@lem6155137 A C f s op h1)). Qed.
Lemma lem6155140 {A C : Type'} (f : A -> C) (s : A -> Prop) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : term36 A C f op s g.
Proof. exact (@lem6155139 A C f s op h1 g). Qed.
Lemma lem6155141 {A C : Type'} (f : A -> C) (op : type1400 C) (s : A -> Prop) (g : A -> C) : (term36 A C f op s g) = (term27 A C f op s g).
Proof. exact (eq_refl (term36 A C f op s g)). Qed.
Lemma lem6155144 {A C : Type'} (f : A -> C) (s : A -> Prop) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : term27 A C f op s g.
Proof. exact (EQ_MP (@lem6155141 A C f op s g) (@lem6155140 A C f s g op h1)). Qed.
Lemma lem6155145 {A C : Type'} (f : A -> C) (s : A -> Prop) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : term27 A C f op s g.
Proof. exact (@lem6155144 A C f s g op h1). Qed.
Lemma lem6155146 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : term37 A B C op s f g.
Proof. exact (@lem6155145 A C g s (term38 A B C op s f g) op h1). Qed.
Lemma lem6155160 {A B : Type'} (f : A -> B) (y : A) : (term39 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6155161 {A C : Type'} (f : A -> C) (y : A) : (term39 A C f y) = (f y).
Proof. exact (@lem6155160 A C f y). Qed.
Lemma lem6155162 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : (term40 A B C op s f g x) = (term41 A B C op s f g x).
Proof. exact (@lem6155161 A C (term38 A B C op s f g) x). Qed.
Lemma lem6155163 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : (term41 A B C op s f g x) = (term42 A B C op s f g x).
Proof. exact (eq_refl (term41 A B C op s f g x)). Qed.
Lemma lem6155164 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) : (term43 A B C op s f g) = (term38 A B C op s f g).
Proof. exact (fun_ext (fun x : A => @lem6155163 A B C op s f g x)). Qed.
Lemma lem6155165 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6155166 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : (term40 A B C op s f g x) = (term41 A B C op s f g x).
Proof. exact (MK_COMB (@lem6155164 A B C op s f g) (@lem6155165 A x)). Qed.
Lemma lem6155167 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6155168 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : (term44 A B C op s f g x) = (term45 A B C op s f g x).
Proof. exact (MK_COMB (@lem6155167 C) (@lem6155166 A B C op s f g x)). Qed.
Lemma lem6155169 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : (term41 A B C op s f g x) = (term42 A B C op s f g x).
Proof. exact (eq_refl (term41 A B C op s f g x)). Qed.
Lemma lem6155170 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : ((term40 A B C op s f g x) = (term41 A B C op s f g x)) = ((term41 A B C op s f g x) = (term42 A B C op s f g x)).
Proof. exact (MK_COMB (@lem6155168 A B C op s f g x) (@lem6155169 A B C op s f g x)). Qed.
Lemma lem6155171 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : (term41 A B C op s f g x) = (term42 A B C op s f g x).
Proof. exact (EQ_MP (@lem6155170 A B C op s f g x) (@lem6155162 A B C op s f g x)). Qed.
Lemma lem6155180 {A C : Type'} (g : A -> C) (x : A) : (term46 A C g x) = (term46 A C g x).
Proof. exact (eq_refl (term46 A C g x)). Qed.
Lemma lem6155181 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : ((g x) = (term41 A B C op s f g x)) = ((g x) = (term42 A B C op s f g x)).
Proof. exact (MK_COMB (@lem6155180 A C g x) (@lem6155171 A B C op s f g x)). Qed.
Lemma lem6155184 {A : Type'} (x : A) (s : A -> Prop) : (term47 A x s) = (term47 A x s).
Proof. exact (eq_refl (term47 A x s)). Qed.
Lemma lem6155185 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : (term48 A B C op s f g x) = (term49 A B C op s f g x).
Proof. exact (MK_COMB (@lem6155184 A x s) (@lem6155181 A B C op s f g x)). Qed.
Lemma lem6155188 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) : (term50 A B C op s f g) = (term51 A B C op s f g).
Proof. exact (fun_ext (fun x : A => @lem6155185 A B C op s f g x)). Qed.
Lemma lem6155189 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6155190 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) : (term52 A B C op s f g) = (term53 A B C op s f g).
Proof. exact (MK_COMB (@lem6155189 A) (@lem6155188 A B C op s f g)). Qed.
Lemma lem6155195 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) : (term53 A B C op s f g) = (term52 A B C op s f g).
Proof. exact (SYM (@lem6155190 A B C op s f g)). Qed.
Lemma lem6155196 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6155197 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : (term54 A B s f x) = (term55 A B f x)) : (term54 A B s f x) = (term55 A B f x).
Proof. exact (h1). Qed.
Lemma lem6155198 {A B C : Type'} (op : type1400 C) (g : A -> C) (x : A) : (term56 A B C op g x) = (term56 A B C op g x).
Proof. exact (eq_refl (term56 A B C op g x)). Qed.
Lemma lem6155199 {A B C : Type'} (op : type1400 C) (g : A -> C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : (term54 A B s f x) = (term55 A B f x)) : (term57 A B C op g s f x) = (term58 A B C op g f x).
Proof. exact (MK_COMB (@lem6155198 A B C op g x) (@lem6155197 A B s f x h1)). Qed.
Lemma lem6155200 {A B C : Type'} (op : type1400 C) (f : A -> B) (g : A -> C) (x : A) : (term58 A B C op g f x) = ((g x) = (term59 A B C op f g x)).
Proof. exact (eq_refl (term58 A B C op g f x)). Qed.
Lemma lem6155201 {A B C : Type'} (op : type1400 C) (g : A -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term60 A B C op g s f x) = (term60 A B C op g s f x).
Proof. exact (eq_refl (term60 A B C op g s f x)). Qed.
Lemma lem6155202 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (f : A -> B) (g : A -> C) (x : A) : ((term57 A B C op g s f x) = (term58 A B C op g f x)) = ((term57 A B C op g s f x) = ((g x) = (term59 A B C op f g x))).
Proof. exact (MK_COMB (@lem6155201 A B C op g s f x) (@lem6155200 A B C op f g x)). Qed.
Lemma lem6155203 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : (term57 A B C op g s f x) = ((g x) = (term42 A B C op s f g x)).
Proof. exact (eq_refl (term57 A B C op g s f x)). Qed.
Lemma lem6155204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6155205 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : (term60 A B C op g s f x) = (term61 A B C op s f g x).
Proof. exact (MK_COMB (@lem6155204) (@lem6155203 A B C op s f g x)). Qed.
Lemma lem6155206 {A B C : Type'} (op : type1400 C) (f : A -> B) (g : A -> C) (x : A) : ((g x) = (term59 A B C op f g x)) = ((g x) = (term59 A B C op f g x)).
Proof. exact (eq_refl ((g x) = (term59 A B C op f g x))). Qed.
Lemma lem6155207 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (f : A -> B) (g : A -> C) (x : A) : ((term57 A B C op g s f x) = ((g x) = (term59 A B C op f g x))) = (((g x) = (term42 A B C op s f g x)) = ((g x) = (term59 A B C op f g x))).
Proof. exact (MK_COMB (@lem6155205 A B C op s f g x) (@lem6155206 A B C op f g x)). Qed.
Lemma lem6155208 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (f : A -> B) (g : A -> C) (x : A) : ((term57 A B C op g s f x) = (term58 A B C op g f x)) = (((g x) = (term42 A B C op s f g x)) = ((g x) = (term59 A B C op f g x))).
Proof. exact (TRANS (@lem6155202 A B C s op f g x) (@lem6155207 A B C s op f g x)). Qed.
Lemma lem6155209 {A B C : Type'} (op : type1400 C) (g : A -> C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : (term54 A B s f x) = (term55 A B f x)) : ((g x) = (term42 A B C op s f g x)) = ((g x) = (term59 A B C op f g x)).
Proof. exact (EQ_MP (@lem6155208 A B C s op f g x) (@lem6155199 A B C op g s f x h1)). Qed.
Lemma lem6155210 {A B C : Type'} (op : type1400 C) (g : A -> C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : (term54 A B s f x) = (term55 A B f x)) : ((g x) = (term59 A B C op f g x)) = ((g x) = (term42 A B C op s f g x)).
Proof. exact (SYM (@lem6155209 A B C op g s f x h1)). Qed.
Lemma lem6155221 {A C : Type'} (s : A -> Prop) (op : type1400 C) (h1 : @FINITE A s) (h2 : @monoidal C op) : term62 A C s op.
Proof. exact (conj (@lem6155102 A s h1) (@lem6155101 C op h2)). Qed.
Lemma lem6155222 {A C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @monoidal C op) (h3 : @IN A x s) : term63 A C x s op.
Proof. exact (conj (@lem6155196 A x s h3) (@lem6155221 A C s op h1 h2)). Qed.
Lemma lem6155232 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem6155233 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term64 B s t).
Proof. exact (@lem6155232 B s t). Qed.
Lemma lem6155234 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term54 A B s f x) = (term55 A B f x)) = (term65 A B s f x).
Proof. exact (@lem6155233 B (term54 A B s f x) (term55 A B f x)). Qed.
Lemma lem6155253 {A C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) : (term66 A C x s op) = (term66 A C x s op).
Proof. exact (eq_refl (term66 A C x s op)). Qed.
Lemma lem6155254 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : (term67 A B C op s f x) = (term68 A B C op s f x).
Proof. exact (MK_COMB (@lem6155253 A C x s op) (@lem6155234 A B s f x)). Qed.
Lemma lem6155257 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : (term68 A B C op s f x) = (term67 A B C op s f x).
Proof. exact (SYM (@lem6155254 A B C op s f x)). Qed.
Lemma lem6155263 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6155264 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6155263 A P x). Qed.
Lemma lem6155265 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6155264 A s x). Qed.
Lemma lem6155266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155267 {A : Type'} (s : A -> Prop) (x : A) : (term69 A x s) = (term70 A s x).
Proof. exact (MK_COMB (@lem6155266) (@lem6155265 A s x)). Qed.
Lemma lem6155270 {A C : Type'} (s : A -> Prop) (op : type1400 C) : (term62 A C s op) = (term62 A C s op).
Proof. exact (eq_refl (term62 A C s op)). Qed.
Lemma lem6155271 {A C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) : (term63 A C x s op) = (term71 A C x s op).
Proof. exact (MK_COMB (@lem6155267 A s x) (@lem6155270 A C s op)). Qed.
Lemma lem6155274 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6155275 {A C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) : (term66 A C x s op) = (term72 A C x s op).
Proof. exact (MK_COMB (@lem6155274) (@lem6155271 A C x s op)). Qed.
Lemma lem6155283 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term73 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem6155284 {B : Type'} (p : B -> Prop) (x : B) : (term73 B x p) = (p x).
Proof. exact (@lem6155283 B p x). Qed.
Lemma lem6155285 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term74 A B x' s f x) = (term75 A B s f x x').
Proof. exact (@lem6155284 B (term76 A B s f x) x'). Qed.
Lemma lem6155286 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term75 A B s f x y) = (term77 A B s f x y).
Proof. exact (eq_refl (term75 A B s f x y)). Qed.
Lemma lem6155287 {B : Type'} (GEN_PVAR_243 : B) : (@SETSPEC B GEN_PVAR_243) = (@SETSPEC B GEN_PVAR_243).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_243)). Qed.
Lemma lem6155288 {A B : Type'} (GEN_PVAR_243 : B) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term78 A B GEN_PVAR_243 s f x y) = (term79 A B GEN_PVAR_243 s f x y).
Proof. exact (MK_COMB (@lem6155287 B GEN_PVAR_243) (@lem6155286 A B s f x y)). Qed.
Lemma lem6155289 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6155290 {A B : Type'} (GEN_PVAR_243 : B) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term80 A B GEN_PVAR_243 s f x y) = (term81 A B GEN_PVAR_243 s f x y).
Proof. exact (MK_COMB (@lem6155288 A B GEN_PVAR_243 s f x y) (@lem6155289 B y)). Qed.
Lemma lem6155291 {A B : Type'} (GEN_PVAR_243 : B) (s : A -> Prop) (f : A -> B) (x : A) : (term82 A B GEN_PVAR_243 s f x) = (term83 A B GEN_PVAR_243 s f x).
Proof. exact (fun_ext (fun y : B => @lem6155290 A B GEN_PVAR_243 s f x y)). Qed.
Lemma lem6155292 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6155293 {A B : Type'} (GEN_PVAR_243 : B) (s : A -> Prop) (f : A -> B) (x : A) : (term84 A B GEN_PVAR_243 s f x) = (term85 A B GEN_PVAR_243 s f x).
Proof. exact (MK_COMB (@lem6155292 B) (@lem6155291 A B GEN_PVAR_243 s f x)). Qed.
Lemma lem6155294 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term86 A B s f x) = (term87 A B s f x).
Proof. exact (fun_ext (fun GEN_PVAR_243 : B => @lem6155293 A B GEN_PVAR_243 s f x)). Qed.
Lemma lem6155295 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem6155296 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term88 A B s f x) = (term54 A B s f x).
Proof. exact (MK_COMB (@lem6155295 B) (@lem6155294 A B s f x)). Qed.
Lemma lem6155297 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem6155298 {A B : Type'} (x : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term74 A B x s f x') = (term89 A B x s f x').
Proof. exact (MK_COMB (@lem6155297 B x) (@lem6155296 A B s f x')). Qed.
Lemma lem6155299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6155300 {A B : Type'} (x : B) (s : A -> Prop) (f : A -> B) (x' : A) : (term90 A B x s f x') = (term91 A B x s f x').
Proof. exact (MK_COMB (@lem6155299) (@lem6155298 A B x s f x')). Qed.
Lemma lem6155301 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term75 A B s f x x') = (term77 A B s f x x').
Proof. exact (eq_refl (term75 A B s f x x')). Qed.
Lemma lem6155302 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : ((term74 A B x' s f x) = (term75 A B s f x x')) = ((term89 A B x' s f x) = (term77 A B s f x x')).
Proof. exact (MK_COMB (@lem6155300 A B x' s f x) (@lem6155301 A B s f x x')). Qed.
Lemma lem6155303 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term89 A B x' s f x) = (term77 A B s f x x').
Proof. exact (EQ_MP (@lem6155302 A B s f x x') (@lem6155285 A B s f x x')). Qed.
Lemma lem6155307 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term92 A B y f s) = (term93 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem6155308 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term92 A B y f s) = (term93 A B y f s).
Proof. exact (@lem6155307 A B y f s). Qed.
Lemma lem6155309 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term92 A B x f s) = (term93 A B x f s).
Proof. exact (@lem6155308 A B x f s). Qed.
Lemma lem6155319 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6155320 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem6155319 A P x). Qed.
Lemma lem6155321 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem6155320 A s x). Qed.
Lemma lem6155322 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term94 A B x f x') = (term94 A B x f x').
Proof. exact (eq_refl (term94 A B x f x')). Qed.
Lemma lem6155323 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term95 A B x f x' s) = (term96 A B x f s x').
Proof. exact (MK_COMB (@lem6155322 A B x f x') (@lem6155321 A s x')). Qed.
Lemma lem6155326 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term97 A B x f s) = (term98 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem6155323 A B x f s x')). Qed.
Lemma lem6155327 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6155328 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term93 A B x f s) = (term99 A B x f s).
Proof. exact (MK_COMB (@lem6155327 A) (@lem6155326 A B x f s)). Qed.
Lemma lem6155333 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term92 A B x f s) = (term99 A B x f s).
Proof. exact (TRANS (@lem6155309 A B x f s) (@lem6155328 A B x f s)). Qed.
Lemma lem6155334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155335 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term100 A B x f s) = (term101 A B x f s).
Proof. exact (MK_COMB (@lem6155334) (@lem6155333 A B x f s)). Qed.
Lemma lem6155338 {A B : Type'} (f : A -> B) (x : A) (x' : B) : ((f x) = x') = ((f x) = x').
Proof. exact (eq_refl ((f x) = x')). Qed.
Lemma lem6155339 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term77 A B s f x x') = (term102 A B s f x x').
Proof. exact (MK_COMB (@lem6155335 A B x' f s) (@lem6155338 A B f x x')). Qed.
Lemma lem6155342 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term89 A B x' s f x) = (term102 A B s f x x').
Proof. exact (TRANS (@lem6155303 A B s f x x') (@lem6155339 A B s f x x')). Qed.
Lemma lem6155343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6155344 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term91 A B x' s f x) = (term103 A B s f x x').
Proof. exact (MK_COMB (@lem6155343) (@lem6155342 A B s f x x')). Qed.
Lemma lem6155346 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term104 A x y s) = (term105 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem6155347 {B : Type'} (y : B) (x : B) (s : B -> Prop) : (term104 B x y s) = (term105 B y x s).
Proof. exact (@lem6155346 B y x s). Qed.
Lemma lem6155348 {A B : Type'} (f : A -> B) (x : A) (x' : B) : (term106 A B x' f x) = (term107 A B f x x').
Proof. exact (@lem6155347 B (f x) x' (@EMPTY B)). Qed.
Lemma lem6155354 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem6155355 {B : Type'} (x : B) : (@IN B x (@EMPTY B)) = False.
Proof. exact (@lem6155354 B x). Qed.
Lemma lem6155356 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term108 A B x f x') = (term108 A B x f x').
Proof. exact (eq_refl (term108 A B x f x')). Qed.
Lemma lem6155357 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term107 A B f x' x) = (term109 A B x f x').
Proof. exact (MK_COMB (@lem6155356 A B x f x') (@lem6155355 B x)). Qed.
Lemma lem6155359 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem6155360 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term109 A B x f x') = (x = (f x')).
Proof. exact (@lem6155359 (x = (f x'))). Qed.
Lemma lem6155363 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term107 A B f x' x) = (x = (f x')).
Proof. exact (TRANS (@lem6155357 A B x f x') (@lem6155360 A B x f x')). Qed.
Lemma lem6155364 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term106 A B x f x') = (x = (f x')).
Proof. exact (TRANS (@lem6155348 A B f x' x) (@lem6155363 A B x f x')). Qed.
Lemma lem6155365 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (x' : A) : ((term89 A B x s f x') = (term106 A B x f x')) = ((term102 A B s f x' x) = (x = (f x'))).
Proof. exact (MK_COMB (@lem6155344 A B s f x' x) (@lem6155364 A B x f x')). Qed.
Lemma lem6155368 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term110 A B s f x) = (term111 A B s f x).
Proof. exact (fun_ext (fun x' : B => @lem6155365 A B s x' f x)). Qed.
Lemma lem6155369 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6155370 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term65 A B s f x) = (term112 A B s f x).
Proof. exact (MK_COMB (@lem6155369 B) (@lem6155368 A B s f x)). Qed.
Lemma lem6155375 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : (term68 A B C op s f x) = (term113 A B C op s f x).
Proof. exact (MK_COMB (@lem6155275 A C x s op) (@lem6155370 A B s f x)). Qed.
Lemma lem6155378 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : (term113 A B C op s f x) = (term68 A B C op s f x).
Proof. exact (SYM (@lem6155375 A B C op s f x)). Qed.
Lemma lem6155380 (p : Prop) : p = (term114 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6155381 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : (term113 A B C op s f x) = (term115 A B C op s f x).
Proof. exact (@lem6155380 (term113 A B C op s f x)). Qed.
Lemma lem6155382 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : (term115 A B C op s f x) = (term113 A B C op s f x).
Proof. exact (SYM (@lem6155381 A B C op s f x)). Qed.
Lemma lem6155383 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B C op s f x) : term116 A B C op s f x.
Proof. exact (h1). Qed.
Lemma lem6155386 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term115 A B C op s f x) : term115 A B C op s f x.
Proof. exact (h1). Qed.
Lemma lem6155387 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : term117 A B C op s f x.
Proof. exact (fun h0 : term115 A B C op s f x => @lem6155386 A B C op s f x h0). Qed.
Lemma lem6155388 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term117 A B C op s f x) : term117 A B C op s f x.
Proof. exact (h1). Qed.
Lemma lem6155389 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term115 A B C op s f x) : term115 A B C op s f x.
Proof. exact (h1). Qed.
Lemma lem6155390 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term115 A B C op s f x) (h2 : term117 A B C op s f x) : term115 A B C op s f x.
Proof. exact (@lem6155388 A B C op s f x h2 (@lem6155389 A B C op s f x h1)). Qed.
Lemma lem6155391 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term115 A B C op s f x) : term118 A B C op s f x.
Proof. exact (fun h0 : term117 A B C op s f x => @lem6155390 A B C op s f x h1 h0). Qed.
Lemma lem6155392 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term117 A B C op s f x) : term117 A B C op s f x.
Proof. exact (h1). Qed.
Lemma lem6155393 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term115 A B C op s f x) (h2 : term117 A B C op s f x) : term115 A B C op s f x.
Proof. exact (@lem6155391 A B C op s f x h1 (@lem6155392 A B C op s f x h2)). Qed.
Lemma lem6155394 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term117 A B C op s f x) : term117 A B C op s f x.
Proof. exact (fun h0 : term115 A B C op s f x => @lem6155393 A B C op s f x h0 h1). Qed.
Lemma lem6155395 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : term119 A B C op s f x.
Proof. exact (fun h0 : term117 A B C op s f x => @lem6155394 A B C op s f x h0). Qed.
Lemma lem6155398 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : term117 A B C op s f x.
Proof. exact (@lem6155395 A B C op s f x (@lem6155387 A B C op s f x)). Qed.
Lemma lem6155399 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : term117 A B C op s f x.
Proof. exact (@lem6155398 A B C op s f x). Qed.
Lemma lem6155417 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6155418 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : (term115 A B C op s f x) = (term120 A B C op s f x).
Proof. exact (@lem6155417 (term116 A B C op s f x)). Qed.
Lemma lem6155420 (t : Prop) : (term121 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6155421 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : (term120 A B C op s f x) = (term113 A B C op s f x).
Proof. exact (@lem6155420 (term113 A B C op s f x)). Qed.
Lemma lem6155424 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : (term115 A B C op s f x) = (term113 A B C op s f x).
Proof. exact (TRANS (@lem6155418 A B C op s f x) (@lem6155421 A B C op s f x)). Qed.
Lemma lem6155469 {A B C : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term122 A B C s f x) = (term123 A B C s f x).
Proof. exact (fun_ext (fun op : type1400 C => @lem6155424 A B C op s f x)). Qed.
Lemma lem6155470 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6155471 {A B C : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term124 A B C s f x) = (term125 A B C s f x).
Proof. exact (MK_COMB (@lem6155470 C) (@lem6155469 A B C s f x)). Qed.
Lemma lem6155476 {A B C : Type'} (f : A -> B) (x : A) : (term126 A B C f x) = (term127 A B C f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6155471 A B C s f x)). Qed.
Lemma lem6155477 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6155478 {A B C : Type'} (f : A -> B) (x : A) : (term128 A B C f x) = (term129 A B C f x).
Proof. exact (MK_COMB (@lem6155477 A) (@lem6155476 A B C f x)). Qed.
Lemma lem6155483 {A B C : Type'} (x : A) : (term130 A B C x) = (term131 A B C x).
Proof. exact (fun_ext (fun f : A -> B => @lem6155478 A B C f x)). Qed.
Lemma lem6155484 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6155485 {A B C : Type'} (x : A) : (term132 A B C x) = (term133 A B C x).
Proof. exact (MK_COMB (@lem6155484 A B) (@lem6155483 A B C x)). Qed.
Lemma lem6155490 {A B C : Type'} : (term134 A B C) = (term135 A B C).
Proof. exact (fun_ext (fun x : A => @lem6155485 A B C x)). Qed.
Lemma lem6155491 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6155500 {A B C : Type'} : (term136 A B C) = (term137 A B C).
Proof. exact (MK_COMB (@lem6155491 A) (@lem6155490 A B C)). Qed.
Lemma lem6155501 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (x = (f x')) = (x = (f x')).
Proof. exact (eq_refl (x = (f x'))). Qed.
Lemma lem6155502 {A B : Type'} (f : A -> B) (x : A) (x' : B) : ((f x) = x') = ((f x) = x').
Proof. exact (eq_refl ((f x) = x')). Qed.
Lemma lem6155507 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term96 A B x f s x') = (term96 A B x f s x').
Proof. exact (eq_refl (term96 A B x f s x')). Qed.
Lemma lem6155508 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term98 A B x f s) = (term98 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem6155507 A B x f s x')). Qed.
Lemma lem6155509 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6155510 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term99 A B x f s) = (term99 A B x f s).
Proof. exact (MK_COMB (@lem6155509 A) (@lem6155508 A B x f s)). Qed.
Lemma lem6155511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155512 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term101 A B x f s) = (term101 A B x f s).
Proof. exact (MK_COMB (@lem6155511) (@lem6155510 A B x f s)). Qed.
Lemma lem6155513 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term102 A B s f x x') = (term102 A B s f x x').
Proof. exact (MK_COMB (@lem6155512 A B x' f s) (@lem6155502 A B f x x')). Qed.
Lemma lem6155514 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6155515 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term103 A B s f x x') = (term103 A B s f x x').
Proof. exact (MK_COMB (@lem6155514) (@lem6155513 A B s f x x')). Qed.
Lemma lem6155516 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (x' : A) : ((term102 A B s f x' x) = (x = (f x'))) = ((term102 A B s f x' x) = (x = (f x'))).
Proof. exact (MK_COMB (@lem6155515 A B s f x' x) (@lem6155501 A B x f x')). Qed.
Lemma lem6155517 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term111 A B s f x) = (term111 A B s f x).
Proof. exact (fun_ext (fun x' : B => @lem6155516 A B s x' f x)). Qed.
Lemma lem6155518 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6155519 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term112 A B s f x) = (term112 A B s f x).
Proof. exact (MK_COMB (@lem6155518 B) (@lem6155517 A B s f x)). Qed.
Lemma lem6155530 {A C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) : (term72 A C x s op) = (term72 A C x s op).
Proof. exact (eq_refl (term72 A C x s op)). Qed.
Lemma lem6155531 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : (term113 A B C op s f x) = (term113 A B C op s f x).
Proof. exact (MK_COMB (@lem6155530 A C x s op) (@lem6155519 A B s f x)). Qed.
Lemma lem6155532 {A B C : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term123 A B C s f x) = (term123 A B C s f x).
Proof. exact (fun_ext (fun op : type1400 C => @lem6155531 A B C op s f x)). Qed.
Lemma lem6155533 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem6155534 {A B C : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term125 A B C s f x) = (term125 A B C s f x).
Proof. exact (MK_COMB (@lem6155533 C) (@lem6155532 A B C s f x)). Qed.
Lemma lem6155535 {A B C : Type'} (f : A -> B) (x : A) : (term127 A B C f x) = (term127 A B C f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6155534 A B C s f x)). Qed.
Lemma lem6155536 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6155537 {A B C : Type'} (f : A -> B) (x : A) : (term129 A B C f x) = (term129 A B C f x).
Proof. exact (MK_COMB (@lem6155536 A) (@lem6155535 A B C f x)). Qed.
Lemma lem6155538 {A B C : Type'} (x : A) : (term131 A B C x) = (term131 A B C x).
Proof. exact (fun_ext (fun f : A -> B => @lem6155537 A B C f x)). Qed.
Lemma lem6155539 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6155540 {A B C : Type'} (x : A) : (term133 A B C x) = (term133 A B C x).
Proof. exact (MK_COMB (@lem6155539 A B) (@lem6155538 A B C x)). Qed.
Lemma lem6155541 {A B C : Type'} : (term135 A B C) = (term135 A B C).
Proof. exact (fun_ext (fun x : A => @lem6155540 A B C x)). Qed.
Lemma lem6155542 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6155543 {A B C : Type'} : (term137 A B C) = (term137 A B C).
Proof. exact (MK_COMB (@lem6155542 A) (@lem6155541 A B C)). Qed.
Lemma lem6155592 {A B C : Type'} : (term136 A B C) = (term137 A B C).
Proof. exact (TRANS (@lem6155500 A B C) (@lem6155543 A B C)). Qed.
Lemma lem6155593 {A B C : Type'} : (term137 A B C) = (term136 A B C).
Proof. exact (SYM (@lem6155592 A B C)). Qed.
Lemma lem6155596 (p : Prop) : p = (term114 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6155597 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : ((term102 A B s f x x') = (x' = (f x))) = (term138 A B s x' f x).
Proof. exact (@lem6155596 ((term102 A B s f x x') = (x' = (f x)))). Qed.
Lemma lem6155598 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term138 A B s x' f x) = ((term102 A B s f x x') = (x' = (f x))).
Proof. exact (SYM (@lem6155597 A B s x' f x)). Qed.
Lemma lem6155599 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term139 A B s x' f x) : term139 A B s x' f x.
Proof. exact (h1). Qed.
Lemma lem6155613 {A C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term71 A C x s op) : term71 A C x s op.
Proof. exact (h1). Qed.
Lemma lem6155622 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x : A) : (term140 A B x' f s x) = (term141 A B x' f s x).
Proof. exact (@lem17045 (x' = (f x)) (s x)). Qed.
Lemma lem6155625 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x : A) : (term96 A B x' f s x) = (term96 A B x' f s x).
Proof. exact (eq_refl (term96 A B x' f s x)). Qed.
Lemma lem6155626 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem6155627 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term144 A B x' f s) = (term145 A B x' f s).
Proof. exact (@lem6155626 A (term98 A B x' f s)). Qed.
Lemma lem6155628 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x : A) : (term146 A B x' f s x) = (term96 A B x' f s x).
Proof. exact (eq_refl (term146 A B x' f s x)). Qed.
Lemma lem6155629 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6155630 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x : A) : (term147 A B x' f s x) = (term140 A B x' f s x).
Proof. exact (MK_COMB (@lem6155629) (@lem6155628 A B x' f s x)). Qed.
Lemma lem6155631 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x : A) : (term147 A B x' f s x) = (term141 A B x' f s x).
Proof. exact (TRANS (@lem6155630 A B x' f s x) (@lem6155622 A B x' f s x)). Qed.
Lemma lem6155632 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term148 A B x' f s) = (term149 A B x' f s).
Proof. exact (fun_ext (fun x : A => @lem6155631 A B x' f s x)). Qed.
Lemma lem6155633 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6155634 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term145 A B x' f s) = (term150 A B x' f s).
Proof. exact (MK_COMB (@lem6155633 A) (@lem6155632 A B x' f s)). Qed.
Lemma lem6155635 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term144 A B x' f s) = (term150 A B x' f s).
Proof. exact (TRANS (@lem6155627 A B x' f s) (@lem6155634 A B x' f s)). Qed.
Lemma lem6155636 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term98 A B x' f s) = (term98 A B x' f s).
Proof. exact (fun_ext (fun x : A => @lem6155625 A B x' f s x)). Qed.
Lemma lem6155637 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6155638 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term99 A B x' f s) = (term99 A B x' f s).
Proof. exact (MK_COMB (@lem6155637 A) (@lem6155636 A B x' f s)). Qed.
Lemma lem6155639 {A B : Type'} (f : A -> B) (x : A) (x' : B) : (term151 A B f x x') = (term151 A B f x x').
Proof. exact (eq_refl (term151 A B f x x')). Qed.
Lemma lem6155640 {A B : Type'} (f : A -> B) (x : A) (x' : B) : ((f x) = x') = ((f x) = x').
Proof. exact (eq_refl ((f x) = x')). Qed.
Lemma lem6155641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6155642 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term152 A B x' f s) = (term153 A B x' f s).
Proof. exact (MK_COMB (@lem6155641) (@lem6155635 A B x' f s)). Qed.
Lemma lem6155643 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term154 A B s f x x') = (term155 A B s f x x').
Proof. exact (MK_COMB (@lem6155642 A B x' f s) (@lem6155639 A B f x x')). Qed.
Lemma lem6155644 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term156 A B s f x x') = (term154 A B s f x x').
Proof. exact (@lem17045 (term99 A B x' f s) ((f x) = x')). Qed.
Lemma lem6155645 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term156 A B s f x x') = (term155 A B s f x x').
Proof. exact (TRANS (@lem6155644 A B s f x x') (@lem6155643 A B s f x x')). Qed.
Lemma lem6155646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155647 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term101 A B x' f s) = (term101 A B x' f s).
Proof. exact (MK_COMB (@lem6155646) (@lem6155638 A B x' f s)). Qed.
Lemma lem6155648 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term102 A B s f x x') = (term102 A B s f x x').
Proof. exact (MK_COMB (@lem6155647 A B x' f s) (@lem6155640 A B f x x')). Qed.
Lemma lem6155649 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term157 A B x' f x) = (term157 A B x' f x).
Proof. exact (eq_refl (term157 A B x' f x)). Qed.
Lemma lem6155650 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (x' = (f x)) = (x' = (f x)).
Proof. exact (eq_refl (x' = (f x))). Qed.
Lemma lem6155651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155652 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term158 A B s f x x') = (term159 A B s f x x').
Proof. exact (MK_COMB (@lem6155651) (@lem6155645 A B s f x x')). Qed.
Lemma lem6155653 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term160 A B s x' f x) = (term161 A B s x' f x).
Proof. exact (MK_COMB (@lem6155652 A B s f x x') (@lem6155650 A B x' f x)). Qed.
Lemma lem6155654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155655 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term162 A B s f x x') = (term162 A B s f x x').
Proof. exact (MK_COMB (@lem6155654) (@lem6155648 A B s f x x')). Qed.
Lemma lem6155656 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term163 A B s x' f x) = (term163 A B s x' f x).
Proof. exact (MK_COMB (@lem6155655 A B s f x x') (@lem6155649 A B x' f x)). Qed.
Lemma lem6155657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6155658 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term164 A B s x' f x) = (term164 A B s x' f x).
Proof. exact (MK_COMB (@lem6155657) (@lem6155656 A B s x' f x)). Qed.
Lemma lem6155659 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term165 A B s x' f x) = (term166 A B s x' f x).
Proof. exact (MK_COMB (@lem6155658 A B s x' f x) (@lem6155653 A B s x' f x)). Qed.
Lemma lem6155660 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term139 A B s x' f x) = (term165 A B s x' f x).
Proof. exact (@lem17646 (term102 A B s f x x') (x' = (f x))). Qed.
Lemma lem6155661 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term139 A B s x' f x) = (term166 A B s x' f x).
Proof. exact (TRANS (@lem6155660 A B s x' f x) (@lem6155659 A B s x' f x)). Qed.
Lemma lem6155744 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6155745 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (@lem6155744 A P Q). Qed.
Lemma lem6155746 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term169 A B s f x x') = (term170 A B s f x x').
Proof. exact (@lem6155745 A (term98 A B x' f s) ((f x) = x')). Qed.
Lemma lem6155747 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x : A) : (term146 A B x' f s x) = (term96 A B x' f s x).
Proof. exact (eq_refl (term146 A B x' f s x)). Qed.
Lemma lem6155748 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term171 A B x' f s) = (term98 A B x' f s).
Proof. exact (fun_ext (fun x : A => @lem6155747 A B x' f s x)). Qed.
Lemma lem6155749 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6155750 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term172 A B x' f s) = (term99 A B x' f s).
Proof. exact (MK_COMB (@lem6155749 A) (@lem6155748 A B x' f s)). Qed.
Lemma lem6155751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155752 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term173 A B x' f s) = (term101 A B x' f s).
Proof. exact (MK_COMB (@lem6155751) (@lem6155750 A B x' f s)). Qed.
Lemma lem6155753 {A B : Type'} (f : A -> B) (x : A) (x' : B) : ((f x) = x') = ((f x) = x').
Proof. exact (eq_refl ((f x) = x')). Qed.
Lemma lem6155754 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term169 A B s f x x') = (term102 A B s f x x').
Proof. exact (MK_COMB (@lem6155752 A B x' f s) (@lem6155753 A B f x x')). Qed.
Lemma lem6155755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6155756 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term174 A B s f x x') = (term103 A B s f x x').
Proof. exact (MK_COMB (@lem6155755) (@lem6155754 A B s f x x')). Qed.
Lemma lem6155757 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term146 A B x' f s x'') = (term96 A B x' f s x'').
Proof. exact (eq_refl (term146 A B x' f s x'')). Qed.
Lemma lem6155758 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155759 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term175 A B x' f s x'') = (term176 A B x' f s x'').
Proof. exact (MK_COMB (@lem6155758) (@lem6155757 A B x' f s x'')). Qed.
Lemma lem6155760 {A B : Type'} (f : A -> B) (x : A) (x' : B) : ((f x) = x') = ((f x) = x').
Proof. exact (eq_refl ((f x) = x')). Qed.
Lemma lem6155761 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (x : A) (x'' : B) : (term177 A B s x' f x x'') = (term178 A B s x' f x x'').
Proof. exact (MK_COMB (@lem6155759 A B x'' f s x') (@lem6155760 A B f x x'')). Qed.
Lemma lem6155762 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term179 A B s f x x') = (term180 A B s f x x').
Proof. exact (fun_ext (fun x'' : A => @lem6155761 A B s x'' f x x')). Qed.
Lemma lem6155763 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6155764 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term170 A B s f x x') = (term181 A B s f x x').
Proof. exact (MK_COMB (@lem6155763 A) (@lem6155762 A B s f x x')). Qed.
Lemma lem6155765 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : ((term169 A B s f x x') = (term170 A B s f x x')) = ((term102 A B s f x x') = (term181 A B s f x x')).
Proof. exact (MK_COMB (@lem6155756 A B s f x x') (@lem6155764 A B s f x x')). Qed.
Lemma lem6155766 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term102 A B s f x x') = (term181 A B s f x x').
Proof. exact (EQ_MP (@lem6155765 A B s f x x') (@lem6155746 A B s f x x')). Qed.
Lemma lem6155767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155768 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term162 A B s f x x') = (term182 A B s f x x').
Proof. exact (MK_COMB (@lem6155767) (@lem6155766 A B s f x x')). Qed.
Lemma lem6155769 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term157 A B x' f x) = (term157 A B x' f x).
Proof. exact (eq_refl (term157 A B x' f x)). Qed.
Lemma lem6155770 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term163 A B s x' f x) = (term183 A B s x' f x).
Proof. exact (MK_COMB (@lem6155768 A B s f x x') (@lem6155769 A B x' f x)). Qed.
Lemma lem6155772 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6155773 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (@lem6155772 A P Q). Qed.
Lemma lem6155774 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term184 A B s x' f x) = (term185 A B s x' f x).
Proof. exact (@lem6155773 A (term180 A B s f x x') (term157 A B x' f x)). Qed.
Lemma lem6155775 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (x : A) (x'' : B) : (term186 A B s f x x'' x') = (term178 A B s x' f x x'').
Proof. exact (eq_refl (term186 A B s f x x'' x')). Qed.
Lemma lem6155776 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term187 A B s f x x') = (term180 A B s f x x').
Proof. exact (fun_ext (fun x'' : A => @lem6155775 A B s x'' f x x')). Qed.
Lemma lem6155777 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6155778 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term188 A B s f x x') = (term181 A B s f x x').
Proof. exact (MK_COMB (@lem6155777 A) (@lem6155776 A B s f x x')). Qed.
Lemma lem6155779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155780 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term189 A B s f x x') = (term182 A B s f x x').
Proof. exact (MK_COMB (@lem6155779) (@lem6155778 A B s f x x')). Qed.
Lemma lem6155781 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term157 A B x' f x) = (term157 A B x' f x).
Proof. exact (eq_refl (term157 A B x' f x)). Qed.
Lemma lem6155782 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term184 A B s x' f x) = (term183 A B s x' f x).
Proof. exact (MK_COMB (@lem6155780 A B s f x x') (@lem6155781 A B x' f x)). Qed.
Lemma lem6155783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6155784 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term190 A B s x' f x) = (term191 A B s x' f x).
Proof. exact (MK_COMB (@lem6155783) (@lem6155782 A B s x' f x)). Qed.
Lemma lem6155785 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (x : A) (x'' : B) : (term186 A B s f x x'' x') = (term178 A B s x' f x x'').
Proof. exact (eq_refl (term186 A B s f x x'' x')). Qed.
Lemma lem6155786 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155787 {A B : Type'} (s : A -> Prop) (x' : A) (f : A -> B) (x : A) (x'' : B) : (term192 A B s f x x'' x') = (term193 A B s x' f x x'').
Proof. exact (MK_COMB (@lem6155786) (@lem6155785 A B s x' f x x'')). Qed.
Lemma lem6155788 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term157 A B x' f x) = (term157 A B x' f x).
Proof. exact (eq_refl (term157 A B x' f x)). Qed.
Lemma lem6155789 {A B : Type'} (s : A -> Prop) (x' : A) (x'' : B) (f : A -> B) (x : A) : (term194 A B s x' x'' f x) = (term195 A B s x' x'' f x).
Proof. exact (MK_COMB (@lem6155787 A B s x' f x x'') (@lem6155788 A B x'' f x)). Qed.
Lemma lem6155790 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term196 A B s x' f x) = (term197 A B s x' f x).
Proof. exact (fun_ext (fun x'' : A => @lem6155789 A B s x'' x' f x)). Qed.
Lemma lem6155791 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6155792 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term185 A B s x' f x) = (term198 A B s x' f x).
Proof. exact (MK_COMB (@lem6155791 A) (@lem6155790 A B s x' f x)). Qed.
Lemma lem6155793 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : ((term184 A B s x' f x) = (term185 A B s x' f x)) = ((term183 A B s x' f x) = (term198 A B s x' f x)).
Proof. exact (MK_COMB (@lem6155784 A B s x' f x) (@lem6155792 A B s x' f x)). Qed.
Lemma lem6155794 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term183 A B s x' f x) = (term198 A B s x' f x).
Proof. exact (EQ_MP (@lem6155793 A B s x' f x) (@lem6155774 A B s x' f x)). Qed.
Lemma lem6155795 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term163 A B s x' f x) = (term198 A B s x' f x).
Proof. exact (TRANS (@lem6155770 A B s x' f x) (@lem6155794 A B s x' f x)). Qed.
Lemma lem6155796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6155797 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term164 A B s x' f x) = (term199 A B s x' f x).
Proof. exact (MK_COMB (@lem6155796) (@lem6155795 A B s x' f x)). Qed.
Lemma lem6155798 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term161 A B s x' f x) = (term161 A B s x' f x).
Proof. exact (eq_refl (term161 A B s x' f x)). Qed.
Lemma lem6155799 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term166 A B s x' f x) = (term200 A B s x' f x).
Proof. exact (MK_COMB (@lem6155797 A B s x' f x) (@lem6155798 A B s x' f x)). Qed.
Lemma lem6155801 {A : Type'} (P : A -> Prop) (Q : Prop) : (term201 A P Q) = (term202 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6155802 {A : Type'} (P : A -> Prop) (Q : Prop) : (term201 A P Q) = (term202 A P Q).
Proof. exact (@lem6155801 A P Q). Qed.
Lemma lem6155803 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term203 A B s x' f x) = (term204 A B s x' f x).
Proof. exact (@lem6155802 A (term197 A B s x' f x) (term161 A B s x' f x)). Qed.
Lemma lem6155804 {A B : Type'} (s : A -> Prop) (x' : A) (x'' : B) (f : A -> B) (x : A) : (term205 A B s x'' f x x') = (term195 A B s x' x'' f x).
Proof. exact (eq_refl (term205 A B s x'' f x x')). Qed.
Lemma lem6155805 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term206 A B s x' f x) = (term197 A B s x' f x).
Proof. exact (fun_ext (fun x'' : A => @lem6155804 A B s x'' x' f x)). Qed.
Lemma lem6155806 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6155807 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term207 A B s x' f x) = (term198 A B s x' f x).
Proof. exact (MK_COMB (@lem6155806 A) (@lem6155805 A B s x' f x)). Qed.
Lemma lem6155808 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6155809 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term208 A B s x' f x) = (term199 A B s x' f x).
Proof. exact (MK_COMB (@lem6155808) (@lem6155807 A B s x' f x)). Qed.
Lemma lem6155810 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term161 A B s x' f x) = (term161 A B s x' f x).
Proof. exact (eq_refl (term161 A B s x' f x)). Qed.
Lemma lem6155811 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term203 A B s x' f x) = (term200 A B s x' f x).
Proof. exact (MK_COMB (@lem6155809 A B s x' f x) (@lem6155810 A B s x' f x)). Qed.
Lemma lem6155812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6155813 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term209 A B s x' f x) = (term210 A B s x' f x).
Proof. exact (MK_COMB (@lem6155812) (@lem6155811 A B s x' f x)). Qed.
Lemma lem6155814 {A B : Type'} (s : A -> Prop) (x' : A) (x'' : B) (f : A -> B) (x : A) : (term205 A B s x'' f x x') = (term195 A B s x' x'' f x).
Proof. exact (eq_refl (term205 A B s x'' f x x')). Qed.
Lemma lem6155815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6155816 {A B : Type'} (s : A -> Prop) (x' : A) (x'' : B) (f : A -> B) (x : A) : (term211 A B s x'' f x x') = (term212 A B s x' x'' f x).
Proof. exact (MK_COMB (@lem6155815) (@lem6155814 A B s x' x'' f x)). Qed.
Lemma lem6155817 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term161 A B s x' f x) = (term161 A B s x' f x).
Proof. exact (eq_refl (term161 A B s x' f x)). Qed.
Lemma lem6155818 {A B : Type'} (x' : A) (s : A -> Prop) (x'' : B) (f : A -> B) (x : A) : (term213 A B x' s x'' f x) = (term214 A B x' s x'' f x).
Proof. exact (MK_COMB (@lem6155816 A B s x' x'' f x) (@lem6155817 A B s x'' f x)). Qed.
Lemma lem6155819 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term215 A B s x' f x) = (term216 A B s x' f x).
Proof. exact (fun_ext (fun x'' : A => @lem6155818 A B x'' s x' f x)). Qed.
Lemma lem6155820 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6155821 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term204 A B s x' f x) = (term217 A B s x' f x).
Proof. exact (MK_COMB (@lem6155820 A) (@lem6155819 A B s x' f x)). Qed.
Lemma lem6155822 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : ((term203 A B s x' f x) = (term204 A B s x' f x)) = ((term200 A B s x' f x) = (term217 A B s x' f x)).
Proof. exact (MK_COMB (@lem6155813 A B s x' f x) (@lem6155821 A B s x' f x)). Qed.
Lemma lem6155823 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term200 A B s x' f x) = (term217 A B s x' f x).
Proof. exact (EQ_MP (@lem6155822 A B s x' f x) (@lem6155803 A B s x' f x)). Qed.
Lemma lem6155825 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term166 A B s x' f x) = (term217 A B s x' f x).
Proof. exact (TRANS (@lem6155799 A B s x' f x) (@lem6155823 A B s x' f x)). Qed.
Lemma lem6155826 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term139 A B s x' f x) = (term217 A B s x' f x).
Proof. exact (TRANS (@lem6155661 A B s x' f x) (@lem6155825 A B s x' f x)). Qed.
Lemma lem6155827 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term139 A B s x' f x) : term217 A B s x' f x.
Proof. exact (EQ_MP (@lem6155826 A B s x' f x) (@lem6155599 A B s x' f x h1)). Qed.
Lemma lem6155828 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term214 A B x'' s x' f x) : term214 A B x'' s x' f x.
Proof. exact (h1). Qed.
Lemma lem6155837 {A C : Type'} (s : A -> Prop) (op : type1400 C) : (term62 A C s op) = (term62 A C s op).
Proof. exact (eq_refl (term62 A C s op)). Qed.
Lemma lem6155842 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6155843 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6155842 A Prop f x). Qed.
Lemma lem6155845 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem6155843 A s x). Qed.
Lemma lem6155846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155847 {A : Type'} (s : A -> Prop) (x : A) : (term70 A s x) = (term218 A s x).
Proof. exact (MK_COMB (@lem6155846) (@lem6155845 A s x)). Qed.
Lemma lem6155848 {A C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) : (term71 A C x s op) = (term219 A C x s op).
Proof. exact (MK_COMB (@lem6155847 A s x) (@lem6155837 A C s op)). Qed.
Lemma lem6155849 {A C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term71 A C x s op) : term219 A C x s op.
Proof. exact (EQ_MP (@lem6155848 A C x s op) (@lem6155613 A C x s op h1)). Qed.
Lemma lem6155856 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (x' = (f x)) = (x' = (f x)).
Proof. exact (eq_refl (x' = (f x))). Qed.
Lemma lem6155865 {A B : Type'} (f : A -> B) (x : A) (x' : B) : (term151 A B f x x') = (term151 A B f x x').
Proof. exact (eq_refl (term151 A B f x x')). Qed.
Lemma lem6155866 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6155871 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6155872 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6155871 A Prop f x). Qed.
Lemma lem6155874 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem6155872 A s x). Qed.
Lemma lem6155875 {A : Type'} (s : A -> Prop) (x : A) : (term220 A s x) = (term221 A s x).
Proof. exact (MK_COMB (@lem6155866) (@lem6155874 A s x)). Qed.
Lemma lem6155886 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term222 A B x' f x) = (term222 A B x' f x).
Proof. exact (eq_refl (term222 A B x' f x)). Qed.
Lemma lem6155887 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x : A) : (term141 A B x' f s x) = (term223 A B x' f s x).
Proof. exact (MK_COMB (@lem6155886 A B x' f x) (@lem6155875 A s x)). Qed.
Lemma lem6155888 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term149 A B x' f s) = (term224 A B x' f s).
Proof. exact (fun_ext (fun x : A => @lem6155887 A B x' f s x)). Qed.
Lemma lem6155889 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6155890 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term150 A B x' f s) = (term225 A B x' f s).
Proof. exact (MK_COMB (@lem6155889 A) (@lem6155888 A B x' f s)). Qed.
Lemma lem6155891 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6155892 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term153 A B x' f s) = (term226 A B x' f s).
Proof. exact (MK_COMB (@lem6155891) (@lem6155890 A B x' f s)). Qed.
Lemma lem6155893 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term155 A B s f x x') = (term227 A B s f x x').
Proof. exact (MK_COMB (@lem6155892 A B x' f s) (@lem6155865 A B f x x')). Qed.
Lemma lem6155894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155895 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term159 A B s f x x') = (term228 A B s f x x').
Proof. exact (MK_COMB (@lem6155894) (@lem6155893 A B s f x x')). Qed.
Lemma lem6155896 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term161 A B s x' f x) = (term229 A B s x' f x).
Proof. exact (MK_COMB (@lem6155895 A B s f x x') (@lem6155856 A B x' f x)). Qed.
Lemma lem6155905 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term157 A B x' f x) = (term157 A B x' f x).
Proof. exact (eq_refl (term157 A B x' f x)). Qed.
Lemma lem6155912 {A B : Type'} (f : A -> B) (x : A) (x' : B) : ((f x) = x') = ((f x) = x').
Proof. exact (eq_refl ((f x) = x')). Qed.
Lemma lem6155917 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6155918 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem6155917 A Prop f x). Qed.
Lemma lem6155920 {A : Type'} (s : A -> Prop) (x'' : A) : (s x'') = (@I (A -> Prop) s x'').
Proof. exact (@lem6155918 A s x''). Qed.
Lemma lem6155929 {A B : Type'} (x' : B) (f : A -> B) (x'' : A) : (term94 A B x' f x'') = (term94 A B x' f x'').
Proof. exact (eq_refl (term94 A B x' f x'')). Qed.
Lemma lem6155930 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term96 A B x' f s x'') = (term230 A B x' f s x'').
Proof. exact (MK_COMB (@lem6155929 A B x' f x'') (@lem6155920 A s x'')). Qed.
Lemma lem6155931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155932 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term176 A B x' f s x'') = (term231 A B x' f s x'').
Proof. exact (MK_COMB (@lem6155931) (@lem6155930 A B x' f s x'')). Qed.
Lemma lem6155933 {A B : Type'} (s : A -> Prop) (x'' : A) (f : A -> B) (x : A) (x' : B) : (term178 A B s x'' f x x') = (term232 A B s x'' f x x').
Proof. exact (MK_COMB (@lem6155932 A B x' f s x'') (@lem6155912 A B f x x')). Qed.
Lemma lem6155934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6155935 {A B : Type'} (s : A -> Prop) (x'' : A) (f : A -> B) (x : A) (x' : B) : (term193 A B s x'' f x x') = (term233 A B s x'' f x x').
Proof. exact (MK_COMB (@lem6155934) (@lem6155933 A B s x'' f x x')). Qed.
Lemma lem6155936 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) : (term195 A B s x'' x' f x) = (term234 A B s x'' x' f x).
Proof. exact (MK_COMB (@lem6155935 A B s x'' f x x') (@lem6155905 A B x' f x)). Qed.
Lemma lem6155937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6155938 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) : (term212 A B s x'' x' f x) = (term235 A B s x'' x' f x).
Proof. exact (MK_COMB (@lem6155937) (@lem6155936 A B s x'' x' f x)). Qed.
Lemma lem6155939 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) : (term214 A B x'' s x' f x) = (term236 A B x'' s x' f x).
Proof. exact (MK_COMB (@lem6155938 A B s x'' x' f x) (@lem6155896 A B s x' f x)). Qed.
Lemma lem6155940 {A B : Type'} (x'' : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term214 A B x'' s x' f x) : term236 A B x'' s x' f x.
Proof. exact (EQ_MP (@lem6155939 A B x'' s x' f x) (@lem6155828 A B x'' s x' f x h1)). Qed.
Lemma lem6155945 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : term234 A B s x'' x' f x.
Proof. exact (h1). Qed.
Lemma lem6155946 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term229 A B s x' f x) : term229 A B s x' f x.
Proof. exact (h1). Qed.
Lemma lem6155948 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : term232 A B s x'' f x x'.
Proof. exact (proj1 (@lem6155945 A B s x'' x' f x h1)). Qed.
Lemma lem6155950 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : term230 A B x' f s x''.
Proof. exact (proj1 (@lem6155948 A B s x'' x' f x h1)). Qed.
Lemma lem6155954 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term229 A B s x' f x) : term227 A B s f x x'.
Proof. exact (proj1 (@lem6155946 A B s x' f x h1)). Qed.
Lemma lem6155955 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (h1 : term225 A B x' f s) : term225 A B x' f s.
Proof. exact (h1). Qed.
Lemma lem6156008 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (x : A) : (term223 A B x' f s x) = (term223 A B x' f s x).
Proof. exact (eq_refl (term223 A B x' f s x)). Qed.
Lemma lem6156009 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term224 A B x' f s) = (term224 A B x' f s).
Proof. exact (fun_ext (fun x : A => @lem6156008 A B x' f s x)). Qed.
Lemma lem6156010 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6156012 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) : (term225 A B x' f s) = (term225 A B x' f s).
Proof. exact (MK_COMB (@lem6156010 A) (@lem6156009 A B x' f s)). Qed.
Lemma lem6156013 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (h1 : term225 A B x' f s) : term225 A B x' f s.
Proof. exact (EQ_MP (@lem6156012 A B x' f s) (@lem6155955 A B x' f s h1)). Qed.
Lemma lem6156033 {A B : Type'} (f : A -> B) (x : A) (x' : B) (h1 : term151 A B f x x') : term151 A B f x x'.
Proof. exact (h1). Qed.
Lemma lem6156034 {A B : Type'} (_77615 : A) (x' : B) (f : A -> B) (s : A -> Prop) (h1 : term225 A B x' f s) : term237 A B x' f s _77615.
Proof. exact (@lem6156013 A B x' f s h1 _77615). Qed.
Lemma lem6156035 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (_77615 : A) : (term237 A B x' f s _77615) = (term223 A B x' f s _77615).
Proof. exact (eq_refl (term237 A B x' f s _77615)). Qed.
Lemma lem6156044 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : term157 A B x' f x.
Proof. exact (proj2 (@lem6155945 A B s x'' x' f x h1)). Qed.
Lemma lem6156046 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : (f x) = x'.
Proof. exact (proj2 (@lem6155948 A B s x'' x' f x h1)). Qed.
Lemma lem6156048 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : x' = (f x'').
Proof. exact (proj1 (@lem6155950 A B s x'' x' f x h1)). Qed.
Lemma lem6156058 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term229 A B s x' f x) : x' = (f x).
Proof. exact (proj2 (@lem6155946 A B s x' f x h1)). Qed.
Lemma lem6156064 {A B : Type'} (_77615 : A) (x' : B) (f : A -> B) (s : A -> Prop) (h1 : term225 A B x' f s) : term223 A B x' f s _77615.
Proof. exact (EQ_MP (@lem6156035 A B x' f s _77615) (@lem6156034 A B _77615 x' f s h1)). Qed.
Lemma lem6156072 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term229 A B s x' f x) : x' = (f x).
Proof. exact (proj2 (@lem6155946 A B s x' f x h1)). Qed.
Lemma lem6156074 {A B : Type'} (f : A -> B) (x : A) (x' : B) (h1 : term151 A B f x x') : term151 A B f x x'.
Proof. exact (h1). Qed.
Lemma lem6156131 {A B : Type'} (f : A -> B) (x : A) : (term238 A B f x) = (term238 A B f x).
Proof. exact (eq_refl (term238 A B f x)). Qed.
Lemma lem6156132 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : (term239 A B f x x') = (term240 A B x f x'').
Proof. exact (MK_COMB (@lem6156131 A B f x) (@lem6156048 A B s x'' x' f x h1)). Qed.
Lemma lem6156133 {A B : Type'} (x'' : A) (f : A -> B) (x : A) : (term240 A B x f x'') = (term241 A B x'' f x).
Proof. exact (eq_refl (term240 A B x f x'')). Qed.
Lemma lem6156134 {A B : Type'} (f : A -> B) (x : A) (x' : B) : (term242 A B f x x') = (term242 A B f x x').
Proof. exact (eq_refl (term242 A B f x x')). Qed.
Lemma lem6156135 {A B : Type'} (x' : B) (x'' : A) (f : A -> B) (x : A) : ((term239 A B f x x') = (term240 A B x f x'')) = ((term239 A B f x x') = (term241 A B x'' f x)).
Proof. exact (MK_COMB (@lem6156134 A B f x x') (@lem6156133 A B x'' f x)). Qed.
Lemma lem6156136 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term239 A B f x x') = (term157 A B x' f x).
Proof. exact (eq_refl (term239 A B f x x')). Qed.
Lemma lem6156137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6156138 {A B : Type'} (x' : B) (f : A -> B) (x : A) : (term242 A B f x x') = (term243 A B x' f x).
Proof. exact (MK_COMB (@lem6156137) (@lem6156136 A B x' f x)). Qed.
Lemma lem6156139 {A B : Type'} (x'' : A) (f : A -> B) (x : A) : (term241 A B x'' f x) = (term241 A B x'' f x).
Proof. exact (eq_refl (term241 A B x'' f x)). Qed.
Lemma lem6156140 {A B : Type'} (x' : B) (x'' : A) (f : A -> B) (x : A) : ((term239 A B f x x') = (term241 A B x'' f x)) = ((term157 A B x' f x) = (term241 A B x'' f x)).
Proof. exact (MK_COMB (@lem6156138 A B x' f x) (@lem6156139 A B x'' f x)). Qed.
Lemma lem6156141 {A B : Type'} (x' : B) (x'' : A) (f : A -> B) (x : A) : ((term239 A B f x x') = (term240 A B x f x'')) = ((term157 A B x' f x) = (term241 A B x'' f x)).
Proof. exact (TRANS (@lem6156135 A B x' x'' f x) (@lem6156140 A B x' x'' f x)). Qed.
Lemma lem6156142 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : (term157 A B x' f x) = (term241 A B x'' f x).
Proof. exact (EQ_MP (@lem6156141 A B x' x'' f x) (@lem6156132 A B s x'' x' f x h1)). Qed.
Lemma lem6156143 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : term241 A B x'' f x.
Proof. exact (EQ_MP (@lem6156142 A B s x'' x' f x h1) (@lem6156044 A B s x'' x' f x h1)). Qed.
Lemma lem6156144 {A B : Type'} (f : A -> B) (x : A) : (term244 A B f x) = (term244 A B f x).
Proof. exact (eq_refl (term244 A B f x)). Qed.
Lemma lem6156145 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : (term245 A B f x x') = (term246 A B x f x'').
Proof. exact (MK_COMB (@lem6156144 A B f x) (@lem6156048 A B s x'' x' f x h1)). Qed.
Lemma lem6156146 {A B : Type'} (x : A) (f : A -> B) (x'' : A) : (term246 A B x f x'') = ((f x) = (f x'')).
Proof. exact (eq_refl (term246 A B x f x'')). Qed.
Lemma lem6156147 {A B : Type'} (f : A -> B) (x : A) (x' : B) : (term247 A B f x x') = (term247 A B f x x').
Proof. exact (eq_refl (term247 A B f x x')). Qed.
Lemma lem6156148 {A B : Type'} (x' : B) (x : A) (f : A -> B) (x'' : A) : ((term245 A B f x x') = (term246 A B x f x'')) = ((term245 A B f x x') = ((f x) = (f x''))).
Proof. exact (MK_COMB (@lem6156147 A B f x x') (@lem6156146 A B x f x'')). Qed.
Lemma lem6156149 {A B : Type'} (f : A -> B) (x : A) (x' : B) : (term245 A B f x x') = ((f x) = x').
Proof. exact (eq_refl (term245 A B f x x')). Qed.
Lemma lem6156150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6156151 {A B : Type'} (f : A -> B) (x : A) (x' : B) : (term247 A B f x x') = (term248 A B f x x').
Proof. exact (MK_COMB (@lem6156150) (@lem6156149 A B f x x')). Qed.
Lemma lem6156152 {A B : Type'} (x : A) (f : A -> B) (x'' : A) : ((f x) = (f x'')) = ((f x) = (f x'')).
Proof. exact (eq_refl ((f x) = (f x''))). Qed.
Lemma lem6156153 {A B : Type'} (x' : B) (x : A) (f : A -> B) (x'' : A) : ((term245 A B f x x') = ((f x) = (f x''))) = (((f x) = x') = ((f x) = (f x''))).
Proof. exact (MK_COMB (@lem6156151 A B f x x') (@lem6156152 A B x f x'')). Qed.
Lemma lem6156154 {A B : Type'} (x' : B) (x : A) (f : A -> B) (x'' : A) : ((term245 A B f x x') = (term246 A B x f x'')) = (((f x) = x') = ((f x) = (f x''))).
Proof. exact (TRANS (@lem6156148 A B x' x f x'') (@lem6156153 A B x' x f x'')). Qed.
Lemma lem6156155 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : ((f x) = x') = ((f x) = (f x'')).
Proof. exact (EQ_MP (@lem6156154 A B x' x f x'') (@lem6156145 A B s x'' x' f x h1)). Qed.
Lemma lem6156227 {A B : Type'} (f : A -> B) (s : A -> Prop) (_77615 : A) : (term249 A B f s _77615) = (term249 A B f s _77615).
Proof. exact (eq_refl (term249 A B f s _77615)). Qed.
Lemma lem6156228 {A B : Type'} (_77615 : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term229 A B s x' f x) : (term250 A B f s _77615 x') = (term251 A B s _77615 f x).
Proof. exact (MK_COMB (@lem6156227 A B f s _77615) (@lem6156058 A B s x' f x h1)). Qed.
Lemma lem6156229 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (_77615 : A) : (term251 A B s _77615 f x) = (term252 A B x f s _77615).
Proof. exact (eq_refl (term251 A B s _77615 f x)). Qed.
Lemma lem6156230 {A B : Type'} (f : A -> B) (s : A -> Prop) (_77615 : A) (x' : B) : (term253 A B f s _77615 x') = (term253 A B f s _77615 x').
Proof. exact (eq_refl (term253 A B f s _77615 x')). Qed.
Lemma lem6156231 {A B : Type'} (x' : B) (x : A) (f : A -> B) (s : A -> Prop) (_77615 : A) : ((term250 A B f s _77615 x') = (term251 A B s _77615 f x)) = ((term250 A B f s _77615 x') = (term252 A B x f s _77615)).
Proof. exact (MK_COMB (@lem6156230 A B f s _77615 x') (@lem6156229 A B x f s _77615)). Qed.
Lemma lem6156232 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (_77615 : A) : (term250 A B f s _77615 x') = (term223 A B x' f s _77615).
Proof. exact (eq_refl (term250 A B f s _77615 x')). Qed.
Lemma lem6156233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6156234 {A B : Type'} (x' : B) (f : A -> B) (s : A -> Prop) (_77615 : A) : (term253 A B f s _77615 x') = (term254 A B x' f s _77615).
Proof. exact (MK_COMB (@lem6156233) (@lem6156232 A B x' f s _77615)). Qed.
Lemma lem6156235 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (_77615 : A) : (term252 A B x f s _77615) = (term252 A B x f s _77615).
Proof. exact (eq_refl (term252 A B x f s _77615)). Qed.
Lemma lem6156236 {A B : Type'} (x' : B) (x : A) (f : A -> B) (s : A -> Prop) (_77615 : A) : ((term250 A B f s _77615 x') = (term252 A B x f s _77615)) = ((term223 A B x' f s _77615) = (term252 A B x f s _77615)).
Proof. exact (MK_COMB (@lem6156234 A B x' f s _77615) (@lem6156235 A B x f s _77615)). Qed.
Lemma lem6156237 {A B : Type'} (x' : B) (x : A) (f : A -> B) (s : A -> Prop) (_77615 : A) : ((term250 A B f s _77615 x') = (term251 A B s _77615 f x)) = ((term223 A B x' f s _77615) = (term252 A B x f s _77615)).
Proof. exact (TRANS (@lem6156231 A B x' x f s _77615) (@lem6156236 A B x' x f s _77615)). Qed.
Lemma lem6156238 {A B : Type'} (_77615 : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term229 A B s x' f x) : (term223 A B x' f s _77615) = (term252 A B x f s _77615).
Proof. exact (EQ_MP (@lem6156237 A B x' x f s _77615) (@lem6156228 A B _77615 s x' f x h1)). Qed.
Lemma lem6156239 {A B : Type'} (_77615 : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term225 A B x' f s) (h2 : term229 A B s x' f x) : term252 A B x f s _77615.
Proof. exact (EQ_MP (@lem6156238 A B _77615 s x' f x h2) (@lem6156064 A B _77615 x' f s h1)). Qed.
Lemma lem6156296 {A B : Type'} (f : A -> B) (x : A) : (term255 A B f x) = (term255 A B f x).
Proof. exact (eq_refl (term255 A B f x)). Qed.
Lemma lem6156297 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term229 A B s x' f x) : (term256 A B f x x') = (term257 A B f x).
Proof. exact (MK_COMB (@lem6156296 A B f x) (@lem6156072 A B s x' f x h1)). Qed.
Lemma lem6156298 {A B : Type'} (f : A -> B) (x : A) : (term257 A B f x) = (term258 A B f x).
Proof. exact (eq_refl (term257 A B f x)). Qed.
Lemma lem6156299 {A B : Type'} (f : A -> B) (x : A) (x' : B) : (term259 A B f x x') = (term259 A B f x x').
Proof. exact (eq_refl (term259 A B f x x')). Qed.
Lemma lem6156300 {A B : Type'} (x' : B) (f : A -> B) (x : A) : ((term256 A B f x x') = (term257 A B f x)) = ((term256 A B f x x') = (term258 A B f x)).
Proof. exact (MK_COMB (@lem6156299 A B f x x') (@lem6156298 A B f x)). Qed.
Lemma lem6156301 {A B : Type'} (f : A -> B) (x : A) (x' : B) : (term256 A B f x x') = (term151 A B f x x').
Proof. exact (eq_refl (term256 A B f x x')). Qed.
Lemma lem6156302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6156303 {A B : Type'} (f : A -> B) (x : A) (x' : B) : (term259 A B f x x') = (term260 A B f x x').
Proof. exact (MK_COMB (@lem6156302) (@lem6156301 A B f x x')). Qed.
Lemma lem6156304 {A B : Type'} (f : A -> B) (x : A) : (term258 A B f x) = (term258 A B f x).
Proof. exact (eq_refl (term258 A B f x)). Qed.
Lemma lem6156305 {A B : Type'} (x' : B) (f : A -> B) (x : A) : ((term256 A B f x x') = (term258 A B f x)) = ((term151 A B f x x') = (term258 A B f x)).
Proof. exact (MK_COMB (@lem6156303 A B f x x') (@lem6156304 A B f x)). Qed.
Lemma lem6156306 {A B : Type'} (x' : B) (f : A -> B) (x : A) : ((term256 A B f x x') = (term257 A B f x)) = ((term151 A B f x x') = (term258 A B f x)).
Proof. exact (TRANS (@lem6156300 A B x' f x) (@lem6156305 A B x' f x)). Qed.
Lemma lem6156307 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term229 A B s x' f x) : (term151 A B f x x') = (term258 A B f x).
Proof. exact (EQ_MP (@lem6156306 A B x' f x) (@lem6156297 A B s x' f x h1)). Qed.
Lemma lem6156308 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term151 A B f x x') (h2 : term229 A B s x' f x) : term258 A B f x.
Proof. exact (EQ_MP (@lem6156307 A B s x' f x h2) (@lem6156074 A B f x x' h1)). Qed.
Lemma lem6156361 {B : Type'} (x : B) (y : B) (z : B) : term261 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem6156369 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : (f x) = (f x'').
Proof. exact (EQ_MP (@lem6156155 A B s x'' x' f x h1) (@lem6156046 A B s x'' x' f x h1)). Qed.
Lemma lem6156370 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : term262 A B x f x''.
Proof. exact (fun h0 : term241 A B x f x'' => @lem6156369 A B s x'' x' f x h1). Qed.
Lemma lem6156372 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6156373 {A B : Type'} (x : A) (f : A -> B) (x'' : A) : (term262 A B x f x'') = ((f x) = (f x'')).
Proof. exact (@lem6156372 ((f x) = (f x''))). Qed.
Lemma lem6156374 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : (f x) = (f x'').
Proof. exact (EQ_MP (@lem6156373 A B x f x'') (@lem6156370 A B s x'' x' f x h1)). Qed.
Lemma lem6156376 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem6156377 {B : Type'} (x : B) : x = x.
Proof. exact (@lem6156376 B x). Qed.
Lemma lem6156378 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem6156377 B (f x)). Qed.
Lemma lem6156379 {A B : Type'} (f : A -> B) (x : A) : term264 A B f x.
Proof. exact (fun h0 : term258 A B f x => @lem6156378 A B f x). Qed.
Lemma lem6156381 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6156382 {A B : Type'} (f : A -> B) (x : A) : (term264 A B f x) = ((f x) = (f x)).
Proof. exact (@lem6156381 ((f x) = (f x))). Qed.
Lemma lem6156383 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem6156382 A B f x) (@lem6156379 A B f x)). Qed.
Lemma lem6156401 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6156402 {B : Type'} (y : B) (x : B) (z : B) : (term265 B x y z) = (term266 B y x z).
Proof. exact (@lem6156401 (y = z) (term267 B x z)). Qed.
Lemma lem6156412 {B : Type'} (x : B) (y : B) : (term268 B x y) = (term268 B x y).
Proof. exact (eq_refl (term268 B x y)). Qed.
Lemma lem6156413 {B : Type'} (y : B) (x : B) (z : B) : (term261 B x y z) = (term269 B y x z).
Proof. exact (MK_COMB (@lem6156412 B x y) (@lem6156402 B y x z)). Qed.
Lemma lem6156417 (q : Prop) (p : Prop) (r : Prop) : (term270 p q r) = (term270 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6156418 {B : Type'} (y : B) (x : B) (z : B) : (term269 B y x z) = (term271 B y x z).
Proof. exact (@lem6156417 (y = z) (term267 B x y) (term267 B x z)). Qed.
Lemma lem6156440 {B : Type'} (y : B) (x : B) (z : B) : (term261 B x y z) = (term271 B y x z).
Proof. exact (TRANS (@lem6156413 B y x z) (@lem6156418 B y x z)). Qed.
Lemma lem6156441 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6156442 {B : Type'} (y : B) (x : B) (z : B) : (term272 B x y z) = (term273 B y x z).
Proof. exact (MK_COMB (@lem6156441) (@lem6156440 B y x z)). Qed.
Lemma lem6156464 {B : Type'} (y : B) (x : B) (z : B) : (term271 B y x z) = (term271 B y x z).
Proof. exact (eq_refl (term271 B y x z)). Qed.
Lemma lem6156465 {B : Type'} (y : B) (x : B) (z : B) : ((term261 B x y z) = (term271 B y x z)) = ((term271 B y x z) = (term271 B y x z)).
Proof. exact (MK_COMB (@lem6156442 B y x z) (@lem6156464 B y x z)). Qed.
Lemma lem6156467 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6156468 (x : Prop) : (x = x) = True.
Proof. exact (@lem6156467 Prop x). Qed.
Lemma lem6156469 {B : Type'} (y : B) (x : B) (z : B) : ((term271 B y x z) = (term271 B y x z)) = True.
Proof. exact (@lem6156468 (term271 B y x z)). Qed.
Lemma lem6156470 {B : Type'} (y : B) (x : B) (z : B) : ((term261 B x y z) = (term271 B y x z)) = True.
Proof. exact (TRANS (@lem6156465 B y x z) (@lem6156469 B y x z)). Qed.
Lemma lem6156471 {B : Type'} (y : B) (x : B) (z : B) : True = ((term261 B x y z) = (term271 B y x z)).
Proof. exact (SYM (@lem6156470 B y x z)). Qed.
Lemma lem6156472 {B : Type'} (y : B) (x : B) (z : B) : (term261 B x y z) = (term271 B y x z).
Proof. exact (EQ_MP (@lem6156471 B y x z) (@lem0)). Qed.
Lemma lem6156473 {B : Type'} (y : B) (x : B) (z : B) : term271 B y x z.
Proof. exact (EQ_MP (@lem6156472 B y x z) (@lem6156361 B x y z)). Qed.
Lemma lem6156475 (b : Prop) (a : Prop) : (a \/ b) = (term274 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6156476 {B : Type'} (x : B) (y : B) (z : B) : (term271 B y x z) = (term275 B x y z).
Proof. exact (@lem6156475 (term276 B y x z) (y = z)). Qed.
Lemma lem6156478 (a : Prop) (b : Prop) : (term277 a b) = (term278 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6156479 {B : Type'} (y : B) (x : B) (z : B) : (term279 B y x z) = (term280 B y x z).
Proof. exact (@lem6156478 (term267 B x y) (term267 B x z)). Qed.
Lemma lem6156481 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6156482 {B : Type'} (x : B) (y : B) : (term281 B x y) = (x = y).
Proof. exact (@lem6156481 (x = y)). Qed.
Lemma lem6156483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6156484 {B : Type'} (x : B) (y : B) : (term282 B x y) = (term283 B x y).
Proof. exact (MK_COMB (@lem6156483) (@lem6156482 B x y)). Qed.
Lemma lem6156486 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6156487 {B : Type'} (x : B) (z : B) : (term281 B x z) = (x = z).
Proof. exact (@lem6156486 (x = z)). Qed.
Lemma lem6156488 {B : Type'} (y : B) (x : B) (z : B) : (term280 B y x z) = (term284 B y x z).
Proof. exact (MK_COMB (@lem6156484 B x y) (@lem6156487 B x z)). Qed.
Lemma lem6156489 {B : Type'} (y : B) (x : B) (z : B) : (term279 B y x z) = (term284 B y x z).
Proof. exact (TRANS (@lem6156479 B y x z) (@lem6156488 B y x z)). Qed.
Lemma lem6156490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6156491 {B : Type'} (y : B) (x : B) (z : B) : (term285 B y x z) = (term286 B y x z).
Proof. exact (MK_COMB (@lem6156490) (@lem6156489 B y x z)). Qed.
Lemma lem6156492 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6156493 {B : Type'} (x : B) (y : B) (z : B) : (term275 B x y z) = (term287 B x y z).
Proof. exact (MK_COMB (@lem6156491 B y x z) (@lem6156492 B y z)). Qed.
Lemma lem6156494 {B : Type'} (x : B) (y : B) (z : B) : (term271 B y x z) = (term287 B x y z).
Proof. exact (TRANS (@lem6156476 B x y z) (@lem6156493 B x y z)). Qed.
Lemma lem6156496 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : term288 A B x'' f x.
Proof. exact (conj (@lem6156374 A B s x'' x' f x h1) (@lem6156383 A B f x)). Qed.
Lemma lem6156498 {B : Type'} (x : B) (y : B) (z : B) : term287 B x y z.
Proof. exact (EQ_MP (@lem6156494 B x y z) (@lem6156473 B y x z)). Qed.
Lemma lem6156499 {B : Type'} (x : B) (y : B) (z : B) : term287 B x y z.
Proof. exact (@lem6156498 B x y z). Qed.
Lemma lem6156500 {A B : Type'} (x'' : A) (f : A -> B) (x : A) : term289 A B x'' f x.
Proof. exact (@lem6156499 B (f x) (f x'') (f x)). Qed.
Lemma lem6156503 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : (f x'') = (f x).
Proof. exact (@lem6156500 A B x'' f x (@lem6156496 A B s x'' x' f x h1)). Qed.
Lemma lem6156504 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : term262 A B x'' f x.
Proof. exact (fun h0 : term241 A B x'' f x => @lem6156503 A B s x'' x' f x h1). Qed.
Lemma lem6156506 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6156507 {A B : Type'} (x'' : A) (f : A -> B) (x : A) : (term262 A B x'' f x) = ((f x'') = (f x)).
Proof. exact (@lem6156506 ((f x'') = (f x))). Qed.
Lemma lem6156508 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : (f x'') = (f x).
Proof. exact (EQ_MP (@lem6156507 A B x'' f x) (@lem6156504 A B s x'' x' f x h1)). Qed.
Lemma lem6156511 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6156513 {A B : Type'} (x'' : A) (f : A -> B) (x : A) : (term241 A B x'' f x) = (term290 A B x'' f x).
Proof. exact (@lem6156511 ((f x'') = (f x))). Qed.
Lemma lem6156516 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : term290 A B x'' f x.
Proof. exact (EQ_MP (@lem6156513 A B x'' f x) (@lem6156143 A B s x'' x' f x h1)). Qed.
Lemma lem6156519 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : False.
Proof. exact (@lem6156516 A B s x'' x' f x h1 (@lem6156508 A B s x'' x' f x h1)). Qed.
Lemma lem6156520 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : term291.
Proof. exact (fun h0 : ~ False => @lem6156519 A B s x'' x' f x h1). Qed.
Lemma lem6156522 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6156523 : term291 = False.
Proof. exact (@lem6156522 False). Qed.
Lemma lem6156585 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem6156586 {B : Type'} (x : B) : x = x.
Proof. exact (@lem6156585 B x). Qed.
Lemma lem6156587 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem6156586 B (f x)). Qed.
Lemma lem6156588 {A B : Type'} (f : A -> B) (x : A) : term264 A B f x.
Proof. exact (fun h0 : term258 A B f x => @lem6156587 A B f x). Qed.
Lemma lem6156590 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6156591 {A B : Type'} (f : A -> B) (x : A) : (term264 A B f x) = ((f x) = (f x)).
Proof. exact (@lem6156590 ((f x) = (f x))). Qed.
Lemma lem6156592 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem6156591 A B f x) (@lem6156588 A B f x)). Qed.
Lemma lem6156594 {A C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term71 A C x s op) : @I (A -> Prop) s x.
Proof. exact (proj1 (@lem6155849 A C x s op h1)). Qed.
Lemma lem6156595 {A C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term71 A C x s op) : term292 A s x.
Proof. exact (fun h0 : term221 A s x => @lem6156594 A C x s op h1). Qed.
Lemma lem6156597 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6156598 {A : Type'} (s : A -> Prop) (x : A) : (term292 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem6156597 (@I (A -> Prop) s x)). Qed.
Lemma lem6156599 {A C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term71 A C x s op) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem6156598 A s x) (@lem6156595 A C x s op h1)). Qed.
Lemma lem6156601 (a : Prop) (b : Prop) : (term293 a b) = (term294 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem6156602 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (_77615 : A) : (term252 A B x f s _77615) = (term295 A B x f s _77615).
Proof. exact (@lem6156601 ((f x) = (f _77615)) (@I (A -> Prop) s _77615)). Qed.
Lemma lem6156604 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6156605 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (_77615 : A) : (term295 A B x f s _77615) = (term296 A B x f s _77615).
Proof. exact (@lem6156604 (term297 A B x f s _77615)). Qed.
Lemma lem6156606 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) (_77615 : A) : (term252 A B x f s _77615) = (term296 A B x f s _77615).
Proof. exact (TRANS (@lem6156602 A B x f s _77615) (@lem6156605 A B x f s _77615)). Qed.
Lemma lem6156608 {A B C : Type'} (f : A -> B) (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term71 A C x s op) : term298 A B f s x.
Proof. exact (conj (@lem6156592 A B f x) (@lem6156599 A C x s op h1)). Qed.
Lemma lem6156610 {A B : Type'} (_77615 : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term225 A B x' f s) (h2 : term229 A B s x' f x) : term296 A B x f s _77615.
Proof. exact (EQ_MP (@lem6156606 A B x f s _77615) (@lem6156239 A B _77615 s x' f x h1 h2)). Qed.
Lemma lem6156611 {A B : Type'} (_77615 : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term225 A B x' f s) (h2 : term229 A B s x' f x) : term296 A B x f s _77615.
Proof. exact (@lem6156610 A B _77615 s x' f x h1 h2). Qed.
Lemma lem6156612 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term225 A B x' f s) (h2 : term229 A B s x' f x) : term299 A B f s x.
Proof. exact (@lem6156611 A B x s x' f x h1 h2). Qed.
Lemma lem6156615 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term225 A B x' f s) (h2 : term71 A C x s op) (h3 : term229 A B s x' f x) : False.
Proof. exact (@lem6156612 A B s x' f x h1 h3 (@lem6156608 A B C f x s op h2)). Qed.
Lemma lem6156616 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term225 A B x' f s) (h2 : term71 A C x s op) (h3 : term229 A B s x' f x) : term291.
Proof. exact (fun h0 : ~ False => @lem6156615 A B C op s x' f x h1 h2 h3). Qed.
Lemma lem6156618 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6156619 : term291 = False.
Proof. exact (@lem6156618 False). Qed.
Lemma lem6156681 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem6156682 {B : Type'} (x : B) : x = x.
Proof. exact (@lem6156681 B x). Qed.
Lemma lem6156683 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem6156682 B (f x)). Qed.
Lemma lem6156684 {A B : Type'} (f : A -> B) (x : A) : term264 A B f x.
Proof. exact (fun h0 : term258 A B f x => @lem6156683 A B f x). Qed.
Lemma lem6156686 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6156687 {A B : Type'} (f : A -> B) (x : A) : (term264 A B f x) = ((f x) = (f x)).
Proof. exact (@lem6156686 ((f x) = (f x))). Qed.
Lemma lem6156688 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem6156687 A B f x) (@lem6156684 A B f x)). Qed.
Lemma lem6156691 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6156693 {A B : Type'} (f : A -> B) (x : A) : (term258 A B f x) = (term300 A B f x).
Proof. exact (@lem6156691 ((f x) = (f x))). Qed.
Lemma lem6156696 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term151 A B f x x') (h2 : term229 A B s x' f x) : term300 A B f x.
Proof. exact (EQ_MP (@lem6156693 A B f x) (@lem6156308 A B s x' f x h1 h2)). Qed.
Lemma lem6156699 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term151 A B f x x') (h2 : term229 A B s x' f x) : False.
Proof. exact (@lem6156696 A B s x' f x h1 h2 (@lem6156688 A B f x)). Qed.
Lemma lem6156700 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term151 A B f x x') (h2 : term229 A B s x' f x) : term291.
Proof. exact (fun h0 : ~ False => @lem6156699 A B s x' f x h1 h2). Qed.
Lemma lem6156702 (p : Prop) : (term263 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6156703 : term291 = False.
Proof. exact (@lem6156702 False). Qed.
Lemma lem6156705 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term151 A B f x x') (h2 : term229 A B s x' f x) : False.
Proof. exact (EQ_MP (@lem6156703) (@lem6156700 A B s x' f x h1 h2)). Qed.
Lemma lem6156706 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term225 A B x' f s) (h2 : term71 A C x s op) (h3 : term229 A B s x' f x) : False.
Proof. exact (EQ_MP (@lem6156619) (@lem6156616 A B C op s x' f x h1 h2 h3)). Qed.
Lemma lem6156707 {A B : Type'} (s : A -> Prop) (x'' : A) (x' : B) (f : A -> B) (x : A) (h1 : term234 A B s x'' x' f x) : False.
Proof. exact (EQ_MP (@lem6156523) (@lem6156520 A B s x'' x' f x h1)). Qed.
Lemma lem6156708 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term151 A B f x x') (h2 : term229 A B s x' f x) : (term151 A B f x x') = False.
Proof. exact (prop_ext (fun h3 : term151 A B f x x' => @lem6156705 A B s x' f x h1 h2) (fun h3 : False => @lem6156074 A B f x x' h1)). Qed.
Lemma lem6156709 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term151 A B f x x') (h2 : term229 A B s x' f x) : False.
Proof. exact (EQ_MP (@lem6156708 A B s x' f x h1 h2) (@lem6156074 A B f x x' h1)). Qed.
Lemma lem6156710 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term151 A B f x x') (h2 : term229 A B s x' f x) : (term151 A B f x x') = False.
Proof. exact (prop_ext (fun h3 : term151 A B f x x' => @lem6156709 A B s x' f x h1 h2) (fun h3 : False => @lem6156033 A B f x x' h1)). Qed.
Lemma lem6156711 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term151 A B f x x') (h2 : term229 A B s x' f x) : False.
Proof. exact (EQ_MP (@lem6156710 A B s x' f x h1 h2) (@lem6156033 A B f x x' h1)). Qed.
Lemma lem6156712 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term151 A B f x x') (h2 : term229 A B s x' f x) : (term151 A B f x x') = False.
Proof. exact (prop_ext (fun h3 : term151 A B f x x' => @lem6156711 A B s x' f x h1 h2) (fun h3 : False => @lem6156033 A B f x x' h1)). Qed.
Lemma lem6156713 {A B : Type'} (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term151 A B f x x') (h2 : term229 A B s x' f x) : False.
Proof. exact (EQ_MP (@lem6156712 A B s x' f x h1 h2) (@lem6156033 A B f x x' h1)). Qed.
Lemma lem6156714 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term225 A B x' f s) (h2 : term71 A C x s op) (h3 : term229 A B s x' f x) : (term225 A B x' f s) = False.
Proof. exact (prop_ext (fun h4 : term225 A B x' f s => @lem6156706 A B C op s x' f x h1 h2 h3) (fun h4 : False => @lem6156013 A B x' f s h1)). Qed.
Lemma lem6156715 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term225 A B x' f s) (h2 : term71 A C x s op) (h3 : term229 A B s x' f x) : False.
Proof. exact (EQ_MP (@lem6156714 A B C op s x' f x h1 h2 h3) (@lem6156013 A B x' f s h1)). Qed.
Lemma lem6156716 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term71 A C x s op) (h2 : term229 A B s x' f x) : False.
Proof. exact (or_elim (@lem6155954 A B s x' f x h2) (fun h0 : term225 A B x' f s => @lem6156715 A B C op s x' f x h0 h1 h2) (fun h0 : term151 A B f x x' => @lem6156713 A B s x' f x h0 h2)). Qed.
Lemma lem6156717 {A B C : Type'} (op : type1400 C) (x'' : A) (s : A -> Prop) (x' : B) (f : A -> B) (x : A) (h1 : term71 A C x s op) (h2 : term214 A B x'' s x' f x) : False.
Proof. exact (or_elim (@lem6155940 A B x'' s x' f x h2) (fun h0 : term234 A B s x'' x' f x => @lem6156707 A B s x'' x' f x h0) (fun h0 : term229 A B s x' f x => @lem6156716 A B C op s x' f x h1 h0)). Qed.
Lemma lem6156718 {A B C : Type'} (x' : B) (f : A -> B) (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term139 A B s x' f x) (h2 : term71 A C x s op) : False.
Proof. exact (ex_elim (@lem6155827 A B s x' f x h1) (fun x'' : A => fun h0 : term216 A B s x' f x x'' => @lem6156717 A B C op x'' s x' f x h2 h0)). Qed.
Lemma lem6156719 {A B C : Type'} (x' : B) (f : A -> B) (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term139 A B s x' f x) (h2 : term71 A C x s op) : (term71 A C x s op) = False.
Proof. exact (prop_ext (fun h3 : term71 A C x s op => @lem6156718 A B C x' f x s op h1 h2) (fun h3 : False => @lem6155613 A C x s op h2)). Qed.
Lemma lem6156720 {A B C : Type'} (x' : B) (f : A -> B) (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term139 A B s x' f x) (h2 : term71 A C x s op) : False.
Proof. exact (EQ_MP (@lem6156719 A B C x' f x s op h1 h2) (@lem6155613 A C x s op h2)). Qed.
Lemma lem6156721 {A B C : Type'} (x' : B) (f : A -> B) (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term139 A B s x' f x) (h2 : term71 A C x s op) : (term139 A B s x' f x) = False.
Proof. exact (prop_ext (fun h3 : term139 A B s x' f x => @lem6156720 A B C x' f x s op h1 h2) (fun h3 : False => @lem6155599 A B s x' f x h1)). Qed.
Lemma lem6156722 {A B C : Type'} (x' : B) (f : A -> B) (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term139 A B s x' f x) (h2 : term71 A C x s op) : False.
Proof. exact (EQ_MP (@lem6156721 A B C x' f x s op h1 h2) (@lem6155599 A B s x' f x h1)). Qed.
Lemma lem6156723 {A B C : Type'} (x' : B) (f : A -> B) (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term71 A C x s op) : term138 A B s x' f x.
Proof. exact (fun h0 : term139 A B s x' f x => @lem6156722 A B C x' f x s op h0 h1). Qed.
Lemma lem6156724 {A B C : Type'} (x' : B) (f : A -> B) (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term71 A C x s op) : (term102 A B s f x x') = (x' = (f x)).
Proof. exact (EQ_MP (@lem6155598 A B s x' f x) (@lem6156723 A B C x' f x s op h1)). Qed.
Lemma lem6156729 {A B C : Type'} (f : A -> B) (x : A) (s : A -> Prop) (op : type1400 C) (h1 : term71 A C x s op) : term112 A B s f x.
Proof. exact (fun x' : B => @lem6156724 A B C x' f x s op h1). Qed.
Lemma lem6156730 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : term113 A B C op s f x.
Proof. exact (fun h0 : term71 A C x s op => @lem6156729 A B C f x s op h0). Qed.
Lemma lem6156735 {A B C : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term125 A B C s f x.
Proof. exact (fun op : type1400 C => @lem6156730 A B C op s f x). Qed.
Lemma lem6156740 {A B C : Type'} (f : A -> B) (x : A) : term129 A B C f x.
Proof. exact (fun s : A -> Prop => @lem6156735 A B C s f x). Qed.
Lemma lem6156745 {A B C : Type'} (x : A) : term133 A B C x.
Proof. exact (fun f : A -> B => @lem6156740 A B C f x). Qed.
Lemma lem6156750 {A B C : Type'} : term137 A B C.
Proof. exact (fun x : A => @lem6156745 A B C x). Qed.
Lemma lem6156751 {A B C : Type'} : term136 A B C.
Proof. exact (EQ_MP (@lem6155593 A B C) (@lem6156750 A B C)). Qed.
Lemma lem6156752 {A B C : Type'} (x : A) : term301 A B C x.
Proof. exact (@lem6156751 A B C x). Qed.
Lemma lem6156753 {A B C : Type'} (x : A) : (term301 A B C x) = (term132 A B C x).
Proof. exact (eq_refl (term301 A B C x)). Qed.
Lemma lem6156754 {A B C : Type'} (x : A) : term132 A B C x.
Proof. exact (EQ_MP (@lem6156753 A B C x) (@lem6156752 A B C x)). Qed.
Lemma lem6156755 {A B C : Type'} (x : A) (f : A -> B) : term302 A B C x f.
Proof. exact (@lem6156754 A B C x f). Qed.
Lemma lem6156756 {A B C : Type'} (f : A -> B) (x : A) : (term302 A B C x f) = (term128 A B C f x).
Proof. exact (eq_refl (term302 A B C x f)). Qed.
Lemma lem6156757 {A B C : Type'} (f : A -> B) (x : A) : term128 A B C f x.
Proof. exact (EQ_MP (@lem6156756 A B C f x) (@lem6156755 A B C x f)). Qed.
Lemma lem6156758 {A B C : Type'} (f : A -> B) (x : A) (s : A -> Prop) : term303 A B C f x s.
Proof. exact (@lem6156757 A B C f x s). Qed.
Lemma lem6156759 {A B C : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term303 A B C f x s) = (term124 A B C s f x).
Proof. exact (eq_refl (term303 A B C f x s)). Qed.
Lemma lem6156760 {A B C : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term124 A B C s f x.
Proof. exact (EQ_MP (@lem6156759 A B C s f x) (@lem6156758 A B C f x s)). Qed.
Lemma lem6156761 {A B C : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 C) : term304 A B C s f x op.
Proof. exact (@lem6156760 A B C s f x op). Qed.
Lemma lem6156762 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : (term304 A B C s f x op) = (term115 A B C op s f x).
Proof. exact (eq_refl (term304 A B C s f x op)). Qed.
Lemma lem6156763 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : term115 A B C op s f x.
Proof. exact (EQ_MP (@lem6156762 A B C op s f x) (@lem6156761 A B C s f x op)). Qed.
Lemma lem6156765 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : term115 A B C op s f x.
Proof. exact (@lem6155399 A B C op s f x (@lem6156763 A B C op s f x)). Qed.
Lemma lem6156766 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B C op s f x) : False.
Proof. exact (@lem6156765 A B C op s f x (@lem6155383 A B C op s f x h1)). Qed.
Lemma lem6156767 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B C op s f x) : (term116 A B C op s f x) = False.
Proof. exact (prop_ext (fun h2 : term116 A B C op s f x => @lem6156766 A B C op s f x h1) (fun h2 : False => @lem6155383 A B C op s f x h1)). Qed.
Lemma lem6156768 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B C op s f x) : False.
Proof. exact (EQ_MP (@lem6156767 A B C op s f x h1) (@lem6155383 A B C op s f x h1)). Qed.
Lemma lem6156769 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : term115 A B C op s f x.
Proof. exact (fun h0 : term116 A B C op s f x => @lem6156768 A B C op s f x h0). Qed.
Lemma lem6156770 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : term113 A B C op s f x.
Proof. exact (EQ_MP (@lem6155382 A B C op s f x) (@lem6156769 A B C op s f x)). Qed.
Lemma lem6156771 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : term68 A B C op s f x.
Proof. exact (EQ_MP (@lem6155378 A B C op s f x) (@lem6156770 A B C op s f x)). Qed.
Lemma lem6156772 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : term67 A B C op s f x.
Proof. exact (EQ_MP (@lem6155257 A B C op s f x) (@lem6156771 A B C op s f x)). Qed.
Lemma lem6156773 {A B C : Type'} (f : A -> B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @monoidal C op) (h3 : @IN A x s) : (term54 A B s f x) = (term55 A B f x).
Proof. exact (@lem6156772 A B C op s f x (@lem6155222 A C op x s h1 h2 h3)). Qed.
Lemma lem6156774 {A B : Type'} (op : type1400 B) : term305 A B op.
Proof. exact (@lem5807175 A B op). Qed.
Lemma lem6156775 {A B : Type'} (op : type1400 B) : (term305 A B op) = (term306 A B op).
Proof. exact (eq_refl (term305 A B op)). Qed.
Lemma lem6156776 {A B : Type'} (op : type1400 B) : term306 A B op.
Proof. exact (EQ_MP (@lem6156775 A B op) (@lem6156774 A B op)). Qed.
Lemma lem6156777 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6156778 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term307 A B op.
Proof. exact (@lem6156776 A B op (@lem6156777 B op h1)). Qed.
Lemma lem6156779 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term308 A B op f.
Proof. exact (@lem6156778 A B op h1 f). Qed.
Lemma lem6156780 {A B : Type'} (op : type1400 B) (f : A -> B) : (term308 A B op f) = (term309 A B op f).
Proof. exact (eq_refl (term308 A B op f)). Qed.
Lemma lem6156781 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term309 A B op f.
Proof. exact (EQ_MP (@lem6156780 A B op f) (@lem6156779 A B f op h1)). Qed.
Lemma lem6156782 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : term310 A B op f x.
Proof. exact (@lem6156781 A B f op h1 x). Qed.
Lemma lem6156783 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term310 A B op f x) = ((term311 A B op x f) = (f x)).
Proof. exact (eq_refl (term310 A B op f x)). Qed.
Lemma lem6156784 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : @monoidal B op) : (term311 A B op x f) = (f x).
Proof. exact (EQ_MP (@lem6156783 A B op f x) (@lem6156782 A B f x op h1)). Qed.
Lemma lem6156790 {C : Type'} (op : type1400 C) : (@monoidal C op) = ((@monoidal C op) = True).
Proof. exact (@lem7 (@monoidal C op)). Qed.
Lemma lem6156799 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : term312 A B op f x.
Proof. exact (fun h0 : @monoidal B op => @lem6156784 A B f x op h0). Qed.
Lemma lem6156800 {B C : Type'} (op : type1400 C) (f : B -> C) (x : B) : term312 B C op f x.
Proof. exact (@lem6156799 B C op f x). Qed.
Lemma lem6156801 {A B C : Type'} (op : type1400 C) (g : A -> C) (f : A -> B) (x : A) : term313 A B C op g f x.
Proof. exact (@lem6156800 B C op (term314 A B C g x) (f x)). Qed.
Lemma lem6156803 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6156790 C op) (@lem6155101 C op h1)). Qed.
Lemma lem6156804 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : True = (@monoidal C op).
Proof. exact (SYM (@lem6156803 C op h1)). Qed.
Lemma lem6156805 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (EQ_MP (@lem6156804 C op h1) (@lem0)). Qed.
Lemma lem6156806 {A B C : Type'} (g : A -> C) (f : A -> B) (x : A) (op : type1400 C) (h1 : @monoidal C op) : (term59 A B C op f g x) = (term315 A B C g f x).
Proof. exact (@lem6156801 A B C op g f x (@lem6156805 C op h1)). Qed.
Lemma lem6156808 {A B : Type'} (f : A -> B) (y : A) : (term39 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6156809 {B C : Type'} (f : B -> C) (y : B) : (term39 B C f y) = (f y).
Proof. exact (@lem6156808 B C f y). Qed.
Lemma lem6156810 {A B C : Type'} (g : A -> C) (f : A -> B) (x : A) : (term316 A B C g f x) = (term315 A B C g f x).
Proof. exact (@lem6156809 B C (term314 A B C g x) (f x)). Qed.
Lemma lem6156811 {A B C : Type'} (y : B) (g : A -> C) (x : A) : (term317 A B C g x y) = (g x).
Proof. exact (eq_refl (term317 A B C g x y)). Qed.
Lemma lem6156812 {A B C : Type'} (g : A -> C) (x : A) : (term318 A B C g x) = (term314 A B C g x).
Proof. exact (fun_ext (fun y : B => @lem6156811 A B C y g x)). Qed.
Lemma lem6156813 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem6156814 {A B C : Type'} (g : A -> C) (f : A -> B) (x : A) : (term316 A B C g f x) = (term315 A B C g f x).
Proof. exact (MK_COMB (@lem6156812 A B C g x) (@lem6156813 A B f x)). Qed.
Lemma lem6156815 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6156816 {A B C : Type'} (g : A -> C) (f : A -> B) (x : A) : (term319 A B C g f x) = (term320 A B C g f x).
Proof. exact (MK_COMB (@lem6156815 C) (@lem6156814 A B C g f x)). Qed.
Lemma lem6156817 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) : (term315 A B C g f x) = (g x).
Proof. exact (eq_refl (term315 A B C g f x)). Qed.
Lemma lem6156818 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) : ((term316 A B C g f x) = (term315 A B C g f x)) = ((term315 A B C g f x) = (g x)).
Proof. exact (MK_COMB (@lem6156816 A B C g f x) (@lem6156817 A B C f g x)). Qed.
Lemma lem6156819 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) : (term315 A B C g f x) = (g x).
Proof. exact (EQ_MP (@lem6156818 A B C f g x) (@lem6156810 A B C g f x)). Qed.
Lemma lem6156820 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) (h1 : @monoidal C op) : (term59 A B C op f g x) = (g x).
Proof. exact (TRANS (@lem6156806 A B C g f x op h1) (@lem6156819 A B C f g x)). Qed.
Lemma lem6156821 {A C : Type'} (g : A -> C) (x : A) : (term46 A C g x) = (term46 A C g x).
Proof. exact (eq_refl (term46 A C g x)). Qed.
Lemma lem6156822 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) (h1 : @monoidal C op) : ((g x) = (term59 A B C op f g x)) = ((g x) = (g x)).
Proof. exact (MK_COMB (@lem6156821 A C g x) (@lem6156820 A B C f g x op h1)). Qed.
Lemma lem6156824 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6156825 {C : Type'} (x : C) : (x = x) = True.
Proof. exact (@lem6156824 C x). Qed.
Lemma lem6156826 {A C : Type'} (g : A -> C) (x : A) : ((g x) = (g x)) = True.
Proof. exact (@lem6156825 C (g x)). Qed.
Lemma lem6156827 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) (h1 : @monoidal C op) : ((g x) = (term59 A B C op f g x)) = True.
Proof. exact (TRANS (@lem6156822 A B C f g x op h1) (@lem6156826 A C g x)). Qed.
Lemma lem6156828 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) (h1 : @monoidal C op) : True = ((g x) = (term59 A B C op f g x)).
Proof. exact (SYM (@lem6156827 A B C f g x op h1)). Qed.
Lemma lem6156829 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) (h1 : @monoidal C op) : (g x) = (term59 A B C op f g x).
Proof. exact (EQ_MP (@lem6156828 A B C f g x op h1) (@lem0)). Qed.
Lemma lem6156830 {A B C : Type'} (g : A -> C) (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) (h1 : @monoidal C op) (h2 : (term54 A B s f x) = (term55 A B f x)) : (g x) = (term42 A B C op s f g x).
Proof. exact (EQ_MP (@lem6155210 A B C op g s f x h2) (@lem6156829 A B C f g x op h1)). Qed.
Lemma lem6156831 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @monoidal C op) (h3 : @IN A x s) : ((term54 A B s f x) = (term55 A B f x)) = ((g x) = (term42 A B C op s f g x)).
Proof. exact (prop_ext (fun h4 : (term54 A B s f x) = (term55 A B f x) => @lem6156830 A B C g op s f x h2 h4) (fun h4 : (g x) = (term42 A B C op s f g x) => @lem6156773 A B C f op x s h1 h2 h3)). Qed.
Lemma lem6156832 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @monoidal C op) (h3 : @IN A x s) : (g x) = (term42 A B C op s f g x).
Proof. exact (EQ_MP (@lem6156831 A B C f g op x s h1 h2 h3) (@lem6156773 A B C f op x s h1 h2 h3)). Qed.
Lemma lem6156833 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (s : A -> Prop) (op : type1400 C) (h1 : @FINITE A s) (h2 : @monoidal C op) : term49 A B C op s f g x.
Proof. exact (fun h0 : @IN A x s => @lem6156832 A B C f g op x s h1 h2 h0). Qed.
Lemma lem6156838 {A B C : Type'} (f : A -> B) (g : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : @FINITE A s) (h2 : @monoidal C op) : term53 A B C op s f g.
Proof. exact (fun x : A => @lem6156833 A B C f g x s op h1 h2). Qed.
Lemma lem6156839 {A B C : Type'} (f : A -> B) (g : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : @FINITE A s) (h2 : @monoidal C op) : term52 A B C op s f g.
Proof. exact (EQ_MP (@lem6155195 A B C op s f g) (@lem6156838 A B C f g s op h1 h2)). Qed.
Lemma lem6156840 {A B C : Type'} (f : A -> B) (g : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : @FINITE A s) (h2 : @monoidal C op) : (@iterate C A op s g) = (term321 A B C op s f g).
Proof. exact (@lem6155146 A B C s f g op h2 (@lem6156839 A B C f g s op h1 h2)). Qed.
Lemma lem6156841 {A B : Type'} (op : type1400 B) : term322 A B op.
Proof. exact (@lem5986609 A B op). Qed.
Lemma lem6156842 {A B : Type'} (op : type1400 B) : (term322 A B op) = (term323 A B op).
Proof. exact (eq_refl (term322 A B op)). Qed.
Lemma lem6156843 {A B : Type'} (op : type1400 B) : term323 A B op.
Proof. exact (EQ_MP (@lem6156842 A B op) (@lem6156841 A B op)). Qed.
Lemma lem6156844 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6156845 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term324 A B op.
Proof. exact (@lem6156843 A B op (@lem6156844 B op h1)). Qed.
Lemma lem6156846 {A B : Type'} (P : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term325 A B op P.
Proof. exact (@lem6156845 A B op h1 P). Qed.
Lemma lem6156847 {A B : Type'} (P : A -> Prop) (op : type1400 B) : (term325 A B op P) = (term326 A B P op).
Proof. exact (eq_refl (term325 A B op P)). Qed.
Lemma lem6156848 {A B : Type'} (P : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term326 A B P op.
Proof. exact (EQ_MP (@lem6156847 A B P op) (@lem6156846 A B P op h1)). Qed.
Lemma lem6156849 {A B : Type'} (P : A -> Prop) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term327 A B P op s.
Proof. exact (@lem6156848 A B P op h1 s). Qed.
Lemma lem6156850 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (op : type1400 B) : (term327 A B P op s) = (term328 A B s P op).
Proof. exact (eq_refl (term327 A B P op s)). Qed.
Lemma lem6156851 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term328 A B s P op.
Proof. exact (EQ_MP (@lem6156850 A B s P op) (@lem6156849 A B P s op h1)). Qed.
Lemma lem6156852 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term329 A B s P op f.
Proof. exact (@lem6156851 A B s P op h1 f). Qed.
Lemma lem6156853 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : (term329 A B s P op f) = ((term330 A B op s P f) = (term331 A B s P f op)).
Proof. exact (eq_refl (term329 A B s P op f)). Qed.
Lemma lem6156854 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term330 A B op s P f) = (term331 A B s P f op).
Proof. exact (EQ_MP (@lem6156853 A B s P f op) (@lem6156852 A B s P f op h1)). Qed.
Lemma lem6156860 {C : Type'} (op : type1400 C) : (@monoidal C op) = ((@monoidal C op) = True).
Proof. exact (@lem7 (@monoidal C op)). Qed.
Lemma lem6156867 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : term332 A B s P f op.
Proof. exact (fun h0 : @monoidal B op => @lem6156854 A B s P f op h0). Qed.
Lemma lem6156868 {B C : Type'} (s : B -> Prop) (P : B -> Prop) (f : B -> C) (op : type1400 C) : term332 B C s P f op.
Proof. exact (@lem6156867 B C s P f op). Qed.
Lemma lem6156869 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) : term333 A B C s f g x op.
Proof. exact (@lem6156868 B C (@IMAGE A B f s) (term244 A B f x) (term314 A B C g x) op). Qed.
Lemma lem6156870 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term245 A B f x y) = ((f x) = y).
Proof. exact (eq_refl (term245 A B f x y)). Qed.
Lemma lem6156871 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term100 A B y f s) = (term100 A B y f s).
Proof. exact (eq_refl (term100 A B y f s)). Qed.
Lemma lem6156872 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term334 A B s f x y) = (term77 A B s f x y).
Proof. exact (MK_COMB (@lem6156871 A B y f s) (@lem6156870 A B f x y)). Qed.
Lemma lem6156873 {B : Type'} (GEN_PVAR_244 : B) : (@SETSPEC B GEN_PVAR_244) = (@SETSPEC B GEN_PVAR_244).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_244)). Qed.
Lemma lem6156874 {A B : Type'} (GEN_PVAR_244 : B) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term335 A B GEN_PVAR_244 s f x y) = (term79 A B GEN_PVAR_244 s f x y).
Proof. exact (MK_COMB (@lem6156873 B GEN_PVAR_244) (@lem6156872 A B s f x y)). Qed.
Lemma lem6156875 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6156876 {A B : Type'} (GEN_PVAR_244 : B) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term336 A B GEN_PVAR_244 s f x y) = (term81 A B GEN_PVAR_244 s f x y).
Proof. exact (MK_COMB (@lem6156874 A B GEN_PVAR_244 s f x y) (@lem6156875 B y)). Qed.
Lemma lem6156877 {A B : Type'} (GEN_PVAR_244 : B) (s : A -> Prop) (f : A -> B) (x : A) : (term337 A B GEN_PVAR_244 s f x) = (term83 A B GEN_PVAR_244 s f x).
Proof. exact (fun_ext (fun y : B => @lem6156876 A B GEN_PVAR_244 s f x y)). Qed.
Lemma lem6156878 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6156879 {A B : Type'} (GEN_PVAR_244 : B) (s : A -> Prop) (f : A -> B) (x : A) : (term338 A B GEN_PVAR_244 s f x) = (term85 A B GEN_PVAR_244 s f x).
Proof. exact (MK_COMB (@lem6156878 B) (@lem6156877 A B GEN_PVAR_244 s f x)). Qed.
Lemma lem6156880 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term339 A B s f x) = (term87 A B s f x).
Proof. exact (fun_ext (fun GEN_PVAR_244 : B => @lem6156879 A B GEN_PVAR_244 s f x)). Qed.
Lemma lem6156881 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem6156882 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term340 A B s f x) = (term54 A B s f x).
Proof. exact (MK_COMB (@lem6156881 B) (@lem6156880 A B s f x)). Qed.
Lemma lem6156883 {B C : Type'} (op : type1400 C) : (@iterate C B op) = (@iterate C B op).
Proof. exact (eq_refl (@iterate C B op)). Qed.
Lemma lem6156884 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (x : A) : (term341 A B C op s f x) = (term342 A B C op s f x).
Proof. exact (MK_COMB (@lem6156883 B C op) (@lem6156882 A B s f x)). Qed.
Lemma lem6156885 {A B C : Type'} (g : A -> C) (x : A) : (term314 A B C g x) = (term314 A B C g x).
Proof. exact (eq_refl (term314 A B C g x)). Qed.
Lemma lem6156886 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : (term343 A B C op s f g x) = (term42 A B C op s f g x).
Proof. exact (MK_COMB (@lem6156884 A B C op s f x) (@lem6156885 A B C g x)). Qed.
Lemma lem6156887 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6156888 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) : (term344 A B C op s f g x) = (term345 A B C op s f g x).
Proof. exact (MK_COMB (@lem6156887 C) (@lem6156886 A B C op s f g x)). Qed.
Lemma lem6156889 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term245 A B f x y) = ((f x) = y).
Proof. exact (eq_refl (term245 A B f x y)). Qed.
Lemma lem6156890 {C : Type'} : (@COND C) = (@COND C).
Proof. exact (eq_refl (@COND C)). Qed.
Lemma lem6156891 {A B C : Type'} (f : A -> B) (x : A) (y : B) : (term346 A B C f x y) = (term347 A B C f x y).
Proof. exact (MK_COMB (@lem6156890 C) (@lem6156889 A B f x y)). Qed.
Lemma lem6156892 {A B C : Type'} (g : A -> C) (x : A) (y : B) : (term317 A B C g x y) = (term317 A B C g x y).
Proof. exact (eq_refl (term317 A B C g x y)). Qed.
Lemma lem6156893 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (y : B) : (term348 A B C f g x y) = (term349 A B C f g x y).
Proof. exact (MK_COMB (@lem6156891 A B C f x y) (@lem6156892 A B C g x y)). Qed.
Lemma lem6156894 {C : Type'} (op : type1400 C) : (@neutral C op) = (@neutral C op).
Proof. exact (eq_refl (@neutral C op)). Qed.
Lemma lem6156895 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (y : B) (op : type1400 C) : (term350 A B C f g x y op) = (term351 A B C f g x y op).
Proof. exact (MK_COMB (@lem6156893 A B C f g x y) (@lem6156894 C op)). Qed.
Lemma lem6156896 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) : (term352 A B C f g x op) = (term353 A B C f g x op).
Proof. exact (fun_ext (fun y : B => @lem6156895 A B C f g x y op)). Qed.
Lemma lem6156897 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term354 A B C op f s) = (term354 A B C op f s).
Proof. exact (eq_refl (term354 A B C op f s)). Qed.
Lemma lem6156898 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) : (term355 A B C s f g x op) = (term356 A B C s f g x op).
Proof. exact (MK_COMB (@lem6156897 A B C op f s) (@lem6156896 A B C f g x op)). Qed.
Lemma lem6156899 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) : ((term343 A B C op s f g x) = (term355 A B C s f g x op)) = ((term42 A B C op s f g x) = (term356 A B C s f g x op)).
Proof. exact (MK_COMB (@lem6156888 A B C op s f g x) (@lem6156898 A B C s f g x op)). Qed.
Lemma lem6156900 {C : Type'} (op : type1400 C) : (term357 C op) = (term357 C op).
Proof. exact (eq_refl (term357 C op)). Qed.
Lemma lem6156901 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) : (term333 A B C s f g x op) = (term358 A B C s f g x op).
Proof. exact (MK_COMB (@lem6156900 C op) (@lem6156899 A B C s f g x op)). Qed.
Lemma lem6156902 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) : term358 A B C s f g x op.
Proof. exact (EQ_MP (@lem6156901 A B C s f g x op) (@lem6156869 A B C s f g x op)). Qed.
Lemma lem6156904 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6156860 C op) (@lem6155101 C op h1)). Qed.
Lemma lem6156905 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : True = (@monoidal C op).
Proof. exact (SYM (@lem6156904 C op h1)). Qed.
Lemma lem6156906 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (EQ_MP (@lem6156905 C op h1) (@lem0)). Qed.
Lemma lem6156907 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) (h1 : @monoidal C op) : (term42 A B C op s f g x) = (term356 A B C s f g x op).
Proof. exact (@lem6156902 A B C s f g x op (@lem6156906 C op h1)). Qed.
Lemma lem6156911 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term359 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6156912 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term360 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6156911 _2963 g t e g' t' e'). Qed.
Lemma lem6156913 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term361 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6156912 _2963 g t e g' t'). Qed.
Lemma lem6156914 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term362 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6156913 _2963 g t e g'). Qed.
Lemma lem6156915 {C : Type'} (g : Prop) (t : C) (e : C) : term362 C g t e.
Proof. exact (@lem6156914 C g t e). Qed.
Lemma lem6156916 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (y : B) (op : type1400 C) : term363 A B C f g x y op.
Proof. exact (@lem6156915 C ((f x) = y) (term317 A B C g x y) (@neutral C op)). Qed.
Lemma lem6156917 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (y : B) (op : type1400 C) (g' : Prop) : term364 A B C f g x y op g'.
Proof. exact (@lem6156916 A B C f g x y op g'). Qed.
Lemma lem6156918 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (y : B) (op : type1400 C) (g' : Prop) : (term364 A B C f g x y op g') = (term365 A B C f g x y op g').
Proof. exact (eq_refl (term364 A B C f g x y op g')). Qed.
Lemma lem6156919 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (y : B) (op : type1400 C) (g' : Prop) : term365 A B C f g x y op g'.
Proof. exact (EQ_MP (@lem6156918 A B C f g x y op g') (@lem6156917 A B C f g x y op g')). Qed.
Lemma lem6156920 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (y : B) (op : type1400 C) (g' : Prop) (t' : C) : term366 A B C f g x y op g' t'.
Proof. exact (@lem6156919 A B C f g x y op g' t'). Qed.
Lemma lem6156921 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (y : B) (op : type1400 C) (g' : Prop) (t' : C) : (term366 A B C f g x y op g' t') = (term367 A B C f g x y op g' t').
Proof. exact (eq_refl (term366 A B C f g x y op g' t')). Qed.
Lemma lem6156922 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (y : B) (op : type1400 C) (g' : Prop) (t' : C) : term367 A B C f g x y op g' t'.
Proof. exact (EQ_MP (@lem6156921 A B C f g x y op g' t') (@lem6156920 A B C f g x y op g' t')). Qed.
Lemma lem6156923 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (y : B) (op : type1400 C) (g' : Prop) (t' : C) (e' : C) : term368 A B C f g x y op g' t' e'.
Proof. exact (@lem6156922 A B C f g x y op g' t' e'). Qed.
Lemma lem6156924 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (y : B) (op : type1400 C) (g' : Prop) (t' : C) (e' : C) : (term368 A B C f g x y op g' t' e') = (term369 A B C f g x y op g' t' e').
Proof. exact (eq_refl (term368 A B C f g x y op g' t' e')). Qed.
Lemma lem6156925 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (y : B) (op : type1400 C) (g' : Prop) (t' : C) (e' : C) : term369 A B C f g x y op g' t' e'.
Proof. exact (EQ_MP (@lem6156924 A B C f g x y op g' t' e') (@lem6156923 A B C f g x y op g' t' e')). Qed.
Lemma lem6156928 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem6156929 {A B C : Type'} (g : A -> C) (op : type1400 C) (f : A -> B) (x : A) (y : B) (t' : C) (e' : C) : term370 A B C g op f x y t' e'.
Proof. exact (@lem6156925 A B C f g x y op ((f x) = y) t' e'). Qed.
Lemma lem6156930 {A B C : Type'} (g : A -> C) (op : type1400 C) (f : A -> B) (x : A) (y : B) (t' : C) (e' : C) : term371 A B C g op f x y t' e'.
Proof. exact (@lem6156929 A B C g op f x y t' e' (@lem6156928 A B f x y)). Qed.
Lemma lem6156933 {A B : Type'} (f : A -> B) (y : A) : (term39 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6156934 {B C : Type'} (f : B -> C) (y : B) : (term39 B C f y) = (f y).
Proof. exact (@lem6156933 B C f y). Qed.
Lemma lem6156935 {A B C : Type'} (g : A -> C) (x : A) (y : B) : (term372 A B C g x y) = (term317 A B C g x y).
Proof. exact (@lem6156934 B C (term314 A B C g x) y). Qed.
Lemma lem6156936 {A B C : Type'} (y : B) (g : A -> C) (x : A) : (term317 A B C g x y) = (g x).
Proof. exact (eq_refl (term317 A B C g x y)). Qed.
Lemma lem6156937 {A B C : Type'} (g : A -> C) (x : A) : (term318 A B C g x) = (term314 A B C g x).
Proof. exact (fun_ext (fun y : B => @lem6156936 A B C y g x)). Qed.
Lemma lem6156938 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6156939 {A B C : Type'} (g : A -> C) (x : A) (y : B) : (term372 A B C g x y) = (term317 A B C g x y).
Proof. exact (MK_COMB (@lem6156937 A B C g x) (@lem6156938 B y)). Qed.
Lemma lem6156940 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6156941 {A B C : Type'} (g : A -> C) (x : A) (y : B) : (term373 A B C g x y) = (term374 A B C g x y).
Proof. exact (MK_COMB (@lem6156940 C) (@lem6156939 A B C g x y)). Qed.
Lemma lem6156942 {A B C : Type'} (y : B) (g : A -> C) (x : A) : (term317 A B C g x y) = (g x).
Proof. exact (eq_refl (term317 A B C g x y)). Qed.
Lemma lem6156943 {A B C : Type'} (y : B) (g : A -> C) (x : A) : ((term372 A B C g x y) = (term317 A B C g x y)) = ((term317 A B C g x y) = (g x)).
Proof. exact (MK_COMB (@lem6156941 A B C g x y) (@lem6156942 A B C y g x)). Qed.
Lemma lem6156944 {A B C : Type'} (y : B) (g : A -> C) (x : A) : (term317 A B C g x y) = (g x).
Proof. exact (EQ_MP (@lem6156943 A B C y g x) (@lem6156935 A B C g x y)). Qed.
Lemma lem6156945 {A B C : Type'} (f : A -> B) (y : B) (g : A -> C) (x : A) : term375 A B C f y g x.
Proof. exact (fun h0 : (f x) = y => @lem6156944 A B C y g x). Qed.
Lemma lem6156946 {A B C : Type'} (op : type1400 C) (f : A -> B) (y : B) (g : A -> C) (x : A) (e' : C) : term376 A B C op f y g x e'.
Proof. exact (@lem6156930 A B C g op f x y (g x) e'). Qed.
Lemma lem6156947 {A B C : Type'} (op : type1400 C) (f : A -> B) (y : B) (g : A -> C) (x : A) (e' : C) : term377 A B C op f y g x e'.
Proof. exact (@lem6156946 A B C op f y g x e' (@lem6156945 A B C f y g x)). Qed.
Lemma lem6156962 {C : Type'} (op : type1400 C) : (@neutral C op) = (@neutral C op).
Proof. exact (eq_refl (@neutral C op)). Qed.
Lemma lem6156963 {A B C : Type'} (f : A -> B) (x : A) (y : B) (op : type1400 C) : term378 A B C f x y op.
Proof. exact (fun h0 : term151 A B f x y => @lem6156962 C op). Qed.
Lemma lem6156964 {A B C : Type'} (f : A -> B) (y : B) (g : A -> C) (x : A) (op : type1400 C) : term379 A B C f y g x op.
Proof. exact (@lem6156947 A B C op f y g x (@neutral C op)). Qed.
Lemma lem6156965 {A B C : Type'} (f : A -> B) (y : B) (g : A -> C) (x : A) (op : type1400 C) : (term351 A B C f g x y op) = (term380 A B C f y g x op).
Proof. exact (@lem6156964 A B C f y g x op (@lem6156963 A B C f x y op)). Qed.
Lemma lem6157014 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) : (term353 A B C f g x op) = (term381 A B C f g x op).
Proof. exact (fun_ext (fun y : B => @lem6156965 A B C f y g x op)). Qed.
Lemma lem6157063 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term354 A B C op f s) = (term354 A B C op f s).
Proof. exact (eq_refl (term354 A B C op f s)). Qed.
Lemma lem6157064 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) : (term356 A B C s f g x op) = (term382 A B C s f g x op).
Proof. exact (MK_COMB (@lem6157063 A B C op f s) (@lem6157014 A B C f g x op)). Qed.
Lemma lem6157113 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) (h1 : @monoidal C op) : (term42 A B C op s f g x) = (term382 A B C s f g x op).
Proof. exact (TRANS (@lem6156907 A B C s f g x op h1) (@lem6157064 A B C s f g x op)). Qed.
Lemma lem6157114 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : (term38 A B C op s f g) = (term383 A B C s f g op).
Proof. exact (fun_ext (fun x : A => @lem6157113 A B C s f g x op h1)). Qed.
Lemma lem6157163 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@iterate C A op s).
Proof. exact (eq_refl (@iterate C A op s)). Qed.
Lemma lem6157164 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : (term321 A B C op s f g) = (term384 A B C s f g op).
Proof. exact (MK_COMB (@lem6157163 A C op s) (@lem6157114 A B C s f g op h1)). Qed.
Lemma lem6157213 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6157214 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : (term385 A B C op s f g) = (term386 A B C s f g op).
Proof. exact (MK_COMB (@lem6157213 C) (@lem6157164 A B C s f g op h1)). Qed.
Lemma lem6157264 {A B : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> B) (op : type1400 B) : term332 A B s P f op.
Proof. exact (fun h0 : @monoidal B op => @lem6156854 A B s P f op h0). Qed.
Lemma lem6157265 {A C : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> C) (op : type1400 C) : term332 A C s P f op.
Proof. exact (@lem6157264 A C s P f op). Qed.
Lemma lem6157266 {A B C : Type'} (s : A -> Prop) (f : A -> B) (y : B) (g : A -> C) (op : type1400 C) : term387 A B C s f y g op.
Proof. exact (@lem6157265 A C s (term388 A B f y) g op). Qed.
Lemma lem6157267 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term389 A B f y x) = ((f x) = y).
Proof. exact (eq_refl (term389 A B f y x)). Qed.
Lemma lem6157268 {A : Type'} (x : A) (s : A -> Prop) : (term69 A x s) = (term69 A x s).
Proof. exact (eq_refl (term69 A x s)). Qed.
Lemma lem6157269 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term390 A B s f y x) = (term391 A B s f x y).
Proof. exact (MK_COMB (@lem6157268 A x s) (@lem6157267 A B f x y)). Qed.
Lemma lem6157270 {A : Type'} (GEN_PVAR_245 : A) : (@SETSPEC A GEN_PVAR_245) = (@SETSPEC A GEN_PVAR_245).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_245)). Qed.
Lemma lem6157271 {A B : Type'} (GEN_PVAR_245 : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term392 A B GEN_PVAR_245 s f y x) = (term393 A B GEN_PVAR_245 s f x y).
Proof. exact (MK_COMB (@lem6157270 A GEN_PVAR_245) (@lem6157269 A B s f x y)). Qed.
Lemma lem6157272 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6157273 {A B : Type'} (GEN_PVAR_245 : A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term394 A B GEN_PVAR_245 s f y x) = (term395 A B GEN_PVAR_245 s f y x).
Proof. exact (MK_COMB (@lem6157271 A B GEN_PVAR_245 s f x y) (@lem6157272 A x)). Qed.
Lemma lem6157274 {A B : Type'} (GEN_PVAR_245 : A) (s : A -> Prop) (f : A -> B) (y : B) : (term396 A B GEN_PVAR_245 s f y) = (term397 A B GEN_PVAR_245 s f y).
Proof. exact (fun_ext (fun x : A => @lem6157273 A B GEN_PVAR_245 s f y x)). Qed.
Lemma lem6157275 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6157276 {A B : Type'} (GEN_PVAR_245 : A) (s : A -> Prop) (f : A -> B) (y : B) : (term398 A B GEN_PVAR_245 s f y) = (term399 A B GEN_PVAR_245 s f y).
Proof. exact (MK_COMB (@lem6157275 A) (@lem6157274 A B GEN_PVAR_245 s f y)). Qed.
Lemma lem6157277 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term400 A B s f y) = (term401 A B s f y).
Proof. exact (fun_ext (fun GEN_PVAR_245 : A => @lem6157276 A B GEN_PVAR_245 s f y)). Qed.
Lemma lem6157278 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6157279 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term402 A B s f y) = (term403 A B s f y).
Proof. exact (MK_COMB (@lem6157278 A) (@lem6157277 A B s f y)). Qed.
Lemma lem6157280 {A C : Type'} (op : type1400 C) : (@iterate C A op) = (@iterate C A op).
Proof. exact (eq_refl (@iterate C A op)). Qed.
Lemma lem6157281 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (y : B) : (term404 A B C op s f y) = (term405 A B C op s f y).
Proof. exact (MK_COMB (@lem6157280 A C op) (@lem6157279 A B s f y)). Qed.
Lemma lem6157282 {A C : Type'} (g : A -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6157283 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (y : B) (g : A -> C) : (term406 A B C op s f y g) = (term407 A B C op s f y g).
Proof. exact (MK_COMB (@lem6157281 A B C op s f y) (@lem6157282 A C g)). Qed.
Lemma lem6157284 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6157285 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : A -> B) (y : B) (g : A -> C) : (term408 A B C op s f y g) = (term409 A B C op s f y g).
Proof. exact (MK_COMB (@lem6157284 C) (@lem6157283 A B C op s f y g)). Qed.
Lemma lem6157286 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term389 A B f y x) = ((f x) = y).
Proof. exact (eq_refl (term389 A B f y x)). Qed.
Lemma lem6157287 {C : Type'} : (@COND C) = (@COND C).
Proof. exact (eq_refl (@COND C)). Qed.
Lemma lem6157288 {A B C : Type'} (f : A -> B) (x : A) (y : B) : (term410 A B C f y x) = (term347 A B C f x y).
Proof. exact (MK_COMB (@lem6157287 C) (@lem6157286 A B f x y)). Qed.
Lemma lem6157289 {A C : Type'} (g : A -> C) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem6157290 {A B C : Type'} (f : A -> B) (y : B) (g : A -> C) (x : A) : (term411 A B C f y g x) = (term412 A B C f y g x).
Proof. exact (MK_COMB (@lem6157288 A B C f x y) (@lem6157289 A C g x)). Qed.
Lemma lem6157291 {C : Type'} (op : type1400 C) : (@neutral C op) = (@neutral C op).
Proof. exact (eq_refl (@neutral C op)). Qed.
Lemma lem6157292 {A B C : Type'} (f : A -> B) (y : B) (g : A -> C) (x : A) (op : type1400 C) : (term413 A B C f y g x op) = (term380 A B C f y g x op).
Proof. exact (MK_COMB (@lem6157290 A B C f y g x) (@lem6157291 C op)). Qed.
Lemma lem6157293 {A B C : Type'} (f : A -> B) (y : B) (g : A -> C) (op : type1400 C) : (term414 A B C f y g op) = (term415 A B C f y g op).
Proof. exact (fun_ext (fun x : A => @lem6157292 A B C f y g x op)). Qed.
Lemma lem6157294 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@iterate C A op s).
Proof. exact (eq_refl (@iterate C A op s)). Qed.
Lemma lem6157295 {A B C : Type'} (s : A -> Prop) (f : A -> B) (y : B) (g : A -> C) (op : type1400 C) : (term416 A B C s f y g op) = (term417 A B C s f y g op).
Proof. exact (MK_COMB (@lem6157294 A C op s) (@lem6157293 A B C f y g op)). Qed.
Lemma lem6157296 {A B C : Type'} (s : A -> Prop) (f : A -> B) (y : B) (g : A -> C) (op : type1400 C) : ((term406 A B C op s f y g) = (term416 A B C s f y g op)) = ((term407 A B C op s f y g) = (term417 A B C s f y g op)).
Proof. exact (MK_COMB (@lem6157285 A B C op s f y g) (@lem6157295 A B C s f y g op)). Qed.
Lemma lem6157297 {C : Type'} (op : type1400 C) : (term357 C op) = (term357 C op).
Proof. exact (eq_refl (term357 C op)). Qed.
Lemma lem6157298 {A B C : Type'} (s : A -> Prop) (f : A -> B) (y : B) (g : A -> C) (op : type1400 C) : (term387 A B C s f y g op) = (term418 A B C s f y g op).
Proof. exact (MK_COMB (@lem6157297 C op) (@lem6157296 A B C s f y g op)). Qed.
Lemma lem6157299 {A B C : Type'} (s : A -> Prop) (f : A -> B) (y : B) (g : A -> C) (op : type1400 C) : term418 A B C s f y g op.
Proof. exact (EQ_MP (@lem6157298 A B C s f y g op) (@lem6157266 A B C s f y g op)). Qed.
Lemma lem6157301 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6156860 C op) (@lem6155101 C op h1)). Qed.
Lemma lem6157302 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : True = (@monoidal C op).
Proof. exact (SYM (@lem6157301 C op h1)). Qed.
Lemma lem6157303 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (EQ_MP (@lem6157302 C op h1) (@lem0)). Qed.
Lemma lem6157304 {A B C : Type'} (s : A -> Prop) (f : A -> B) (y : B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : (term407 A B C op s f y g) = (term417 A B C s f y g op).
Proof. exact (@lem6157299 A B C s f y g op (@lem6157303 C op h1)). Qed.
Lemma lem6157353 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : (term419 A B C op s f g) = (term420 A B C s f g op).
Proof. exact (fun_ext (fun y : B => @lem6157304 A B C s f y g op h1)). Qed.
Lemma lem6157402 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term354 A B C op f s) = (term354 A B C op f s).
Proof. exact (eq_refl (term354 A B C op f s)). Qed.
Lemma lem6157403 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : (term20 A B C op s f g) = (term421 A B C s f g op).
Proof. exact (MK_COMB (@lem6157402 A B C op f s) (@lem6157353 A B C s f g op h1)). Qed.
Lemma lem6157452 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : ((term321 A B C op s f g) = (term20 A B C op s f g)) = ((term384 A B C s f g op) = (term421 A B C s f g op)).
Proof. exact (MK_COMB (@lem6157214 A B C s f g op h1) (@lem6157403 A B C s f g op h1)). Qed.
Lemma lem6157551 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : ((term384 A B C s f g op) = (term421 A B C s f g op)) = ((term321 A B C op s f g) = (term20 A B C op s f g)).
Proof. exact (SYM (@lem6157452 A B C s f g op h1)). Qed.
Lemma lem6157557 {A B C : Type'} (op : type1400 C) : term422 A B C op.
Proof. exact (@lem6113745 A B C op). Qed.
Lemma lem6157558 {A B C : Type'} (op : type1400 C) : (term422 A B C op) = (term423 A B C op).
Proof. exact (eq_refl (term422 A B C op)). Qed.
Lemma lem6157561 {A B C : Type'} (op : type1400 C) : term423 A B C op.
Proof. exact (EQ_MP (@lem6157558 A B C op) (@lem6157557 A B C op)). Qed.
Lemma lem6157562 {A B C : Type'} (op : type1400 C) : term423 A B C op.
Proof. exact (@lem6157561 A B C op). Qed.
Lemma lem6157563 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term424 A B C op.
Proof. exact (@lem6157562 A B C op (@lem6155101 C op h1)). Qed.
Lemma lem6157564 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term425 A B C op f.
Proof. exact (@lem6157563 A B C op h1 f). Qed.
Lemma lem6157565 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term425 A B C op f) = (term426 A B C op f).
Proof. exact (eq_refl (term425 A B C op f)). Qed.
Lemma lem6157566 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term426 A B C op f.
Proof. exact (EQ_MP (@lem6157565 A B C op f) (@lem6157564 A B C f op h1)). Qed.
Lemma lem6157567 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term427 A B C op f s.
Proof. exact (@lem6157566 A B C f op h1 s). Qed.
Lemma lem6157568 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term427 A B C op f s) = (term428 A B C op s f).
Proof. exact (eq_refl (term427 A B C op f s)). Qed.
Lemma lem6157569 {A B C : Type'} (s : A -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term428 A B C op s f.
Proof. exact (EQ_MP (@lem6157568 A B C op s f) (@lem6157567 A B C f s op h1)). Qed.
Lemma lem6157570 {A B C : Type'} (s : A -> Prop) (f : type1412 A B C) (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term429 A B C op s f t.
Proof. exact (@lem6157569 A B C s f op h1 t). Qed.
Lemma lem6157571 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term429 A B C op s f t) = (term430 A B C t op s f).
Proof. exact (eq_refl (term429 A B C op s f t)). Qed.
Lemma lem6157574 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term430 A B C t op s f.
Proof. exact (EQ_MP (@lem6157571 A B C t op s f) (@lem6157570 A B C s f t op h1)). Qed.
Lemma lem6157575 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term430 A B C t op s f.
Proof. exact (@lem6157574 A B C t s f op h1). Qed.
Lemma lem6157576 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : term431 A B C s f g op.
Proof. exact (@lem6157575 A B C (@IMAGE A B f s) s (term432 A B C f g op) op h1). Qed.
Lemma lem6157577 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) : (term433 A B C f g op x) = (term381 A B C f g x op).
Proof. exact (eq_refl (term433 A B C f g op x)). Qed.
Lemma lem6157578 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term354 A B C op f s) = (term354 A B C op f s).
Proof. exact (eq_refl (term354 A B C op f s)). Qed.
Lemma lem6157579 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) : (term434 A B C s f g op x) = (term382 A B C s f g x op).
Proof. exact (MK_COMB (@lem6157578 A B C op f s) (@lem6157577 A B C f g x op)). Qed.
Lemma lem6157580 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term435 A B C s f g op) = (term383 A B C s f g op).
Proof. exact (fun_ext (fun x : A => @lem6157579 A B C s f g x op)). Qed.
Lemma lem6157581 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@iterate C A op s).
Proof. exact (eq_refl (@iterate C A op s)). Qed.
Lemma lem6157582 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term436 A B C s f g op) = (term384 A B C s f g op).
Proof. exact (MK_COMB (@lem6157581 A C op s) (@lem6157580 A B C s f g op)). Qed.
Lemma lem6157583 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6157584 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term437 A B C s f g op) = (term386 A B C s f g op).
Proof. exact (MK_COMB (@lem6157583 C) (@lem6157582 A B C s f g op)). Qed.
Lemma lem6157585 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) : (term433 A B C f g op x) = (term381 A B C f g x op).
Proof. exact (eq_refl (term433 A B C f g op x)). Qed.
Lemma lem6157586 {B : Type'} (j : B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem6157587 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) (j : B) : (term438 A B C f g op x j) = (term439 A B C f g x op j).
Proof. exact (MK_COMB (@lem6157585 A B C f g x op) (@lem6157586 B j)). Qed.
Lemma lem6157588 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (j : B) : (term440 A B C f g op j) = (term441 A B C f g op j).
Proof. exact (fun_ext (fun x : A => @lem6157587 A B C f g x op j)). Qed.
Lemma lem6157589 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@iterate C A op s).
Proof. exact (eq_refl (@iterate C A op s)). Qed.
Lemma lem6157590 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (j : B) : (term442 A B C s f g op j) = (term443 A B C s f g op j).
Proof. exact (MK_COMB (@lem6157589 A C op s) (@lem6157588 A B C f g op j)). Qed.
Lemma lem6157591 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term444 A B C s f g op) = (term445 A B C s f g op).
Proof. exact (fun_ext (fun j : B => @lem6157590 A B C s f g op j)). Qed.
Lemma lem6157592 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term354 A B C op f s) = (term354 A B C op f s).
Proof. exact (eq_refl (term354 A B C op f s)). Qed.
Lemma lem6157593 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term446 A B C s f g op) = (term447 A B C s f g op).
Proof. exact (MK_COMB (@lem6157592 A B C op f s) (@lem6157591 A B C s f g op)). Qed.
Lemma lem6157594 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : ((term436 A B C s f g op) = (term446 A B C s f g op)) = ((term384 A B C s f g op) = (term447 A B C s f g op)).
Proof. exact (MK_COMB (@lem6157584 A B C s f g op) (@lem6157593 A B C s f g op)). Qed.
Lemma lem6157595 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term448 A B f s) = (term448 A B f s).
Proof. exact (eq_refl (term448 A B f s)). Qed.
Lemma lem6157596 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term431 A B C s f g op) = (term449 A B C s f g op).
Proof. exact (MK_COMB (@lem6157595 A B f s) (@lem6157594 A B C s f g op)). Qed.
Lemma lem6157597 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : term449 A B C s f g op.
Proof. exact (EQ_MP (@lem6157596 A B C s f g op) (@lem6157576 A B C s f g op h1)). Qed.
Lemma lem6157598 {A B : Type'} (f : A -> B) : term450 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem6157599 {A B : Type'} (f : A -> B) : (term450 A B f) = (term451 A B f).
Proof. exact (eq_refl (term450 A B f)). Qed.
Lemma lem6157600 {A B : Type'} (f : A -> B) : term451 A B f.
Proof. exact (EQ_MP (@lem6157599 A B f) (@lem6157598 A B f)). Qed.
Lemma lem6157601 {A B : Type'} (f : A -> B) (s : A -> Prop) : term452 A B f s.
Proof. exact (@lem6157600 A B f s). Qed.
Lemma lem6157602 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term452 A B f s) = (term453 A B f s).
Proof. exact (eq_refl (term452 A B f s)). Qed.
Lemma lem6157603 {A B : Type'} (f : A -> B) (s : A -> Prop) : term453 A B f s.
Proof. exact (EQ_MP (@lem6157602 A B f s) (@lem6157601 A B f s)). Qed.
Lemma lem6157604 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6157605 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term454 A B f s.
Proof. exact (@lem6157603 A B f s (@lem6157604 A s h1)). Qed.
Lemma lem6157606 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term454 A B f s) = ((term454 A B f s) = True).
Proof. exact (@lem7 (term454 A B f s)). Qed.
Lemma lem6157607 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term454 A B f s) = True.
Proof. exact (EQ_MP (@lem6157606 A B f s) (@lem6157605 A B f s h1)). Qed.
Lemma lem6157615 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6157620 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term455 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6157621 (p : Prop) (q : Prop) (p' : Prop) : term456 p q p'.
Proof. exact (fun q' : Prop => @lem6157620 p q p' q'). Qed.
Lemma lem6157622 (p : Prop) (q : Prop) : term457 p q.
Proof. exact (fun p' : Prop => @lem6157621 p q p'). Qed.
Lemma lem6157623 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : term458 A B C s f g op.
Proof. exact (@lem6157622 (term449 A B C s f g op) ((term384 A B C s f g op) = (term421 A B C s f g op))). Qed.
Lemma lem6157624 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (p' : Prop) : term459 A B C s f g op p'.
Proof. exact (@lem6157623 A B C s f g op p'). Qed.
Lemma lem6157625 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (p' : Prop) : (term459 A B C s f g op p') = (term460 A B C s f g op p').
Proof. exact (eq_refl (term459 A B C s f g op p')). Qed.
Lemma lem6157626 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (p' : Prop) : term460 A B C s f g op p'.
Proof. exact (EQ_MP (@lem6157625 A B C s f g op p') (@lem6157624 A B C s f g op p')). Qed.
Lemma lem6157627 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (p' : Prop) (q' : Prop) : term461 A B C s f g op p' q'.
Proof. exact (@lem6157626 A B C s f g op p' q'). Qed.
Lemma lem6157628 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (p' : Prop) (q' : Prop) : (term461 A B C s f g op p' q') = (term462 A B C s f g op p' q').
Proof. exact (eq_refl (term461 A B C s f g op p' q')). Qed.
Lemma lem6157629 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (p' : Prop) (q' : Prop) : term462 A B C s f g op p' q'.
Proof. exact (EQ_MP (@lem6157628 A B C s f g op p' q') (@lem6157627 A B C s f g op p' q')). Qed.
Lemma lem6157633 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term455 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6157634 (p : Prop) (q : Prop) (p' : Prop) : term456 p q p'.
Proof. exact (fun q' : Prop => @lem6157633 p q p' q'). Qed.
Lemma lem6157635 (p : Prop) (q : Prop) : term457 p q.
Proof. exact (fun p' : Prop => @lem6157634 p q p'). Qed.
Lemma lem6157636 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : term463 A B C s f g op.
Proof. exact (@lem6157635 (term464 A B f s) ((term384 A B C s f g op) = (term447 A B C s f g op))). Qed.
Lemma lem6157637 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (p' : Prop) : term465 A B C s f g op p'.
Proof. exact (@lem6157636 A B C s f g op p'). Qed.
Lemma lem6157638 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (p' : Prop) : (term465 A B C s f g op p') = (term466 A B C s f g op p').
Proof. exact (eq_refl (term465 A B C s f g op p')). Qed.
Lemma lem6157639 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (p' : Prop) : term466 A B C s f g op p'.
Proof. exact (EQ_MP (@lem6157638 A B C s f g op p') (@lem6157637 A B C s f g op p')). Qed.
Lemma lem6157640 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (p' : Prop) (q' : Prop) : term467 A B C s f g op p' q'.
Proof. exact (@lem6157639 A B C s f g op p' q'). Qed.
Lemma lem6157641 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (p' : Prop) (q' : Prop) : (term467 A B C s f g op p' q') = (term468 A B C s f g op p' q').
Proof. exact (eq_refl (term467 A B C s f g op p' q')). Qed.
Lemma lem6157642 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (p' : Prop) (q' : Prop) : term468 A B C s f g op p' q'.
Proof. exact (EQ_MP (@lem6157641 A B C s f g op p' q') (@lem6157640 A B C s f g op p' q')). Qed.
Lemma lem6157646 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6157615 A s) (@lem6155102 A s h1)). Qed.
Lemma lem6157647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6157648 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term469 A s) = (and True).
Proof. exact (MK_COMB (@lem6157647) (@lem6157646 A s h1)). Qed.
Lemma lem6157650 {A B : Type'} (f : A -> B) (s : A -> Prop) : term470 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem6157607 A B f s h0). Qed.
Lemma lem6157651 {A B : Type'} (f : A -> B) (s : A -> Prop) : term470 A B f s.
Proof. exact (@lem6157650 A B f s). Qed.
Lemma lem6157653 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6157615 A s) (@lem6155102 A s h1)). Qed.
Lemma lem6157654 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem6157653 A s h1)). Qed.
Lemma lem6157655 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem6157654 A s h1) (@lem0)). Qed.
Lemma lem6157656 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term454 A B f s) = True.
Proof. exact (@lem6157651 A B f s (@lem6157655 A s h1)). Qed.
Lemma lem6157657 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term464 A B f s) = (True /\ True).
Proof. exact (MK_COMB (@lem6157648 A s h1) (@lem6157656 A B f s h1)). Qed.
Lemma lem6157659 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6157660 : (True /\ True) = True.
Proof. exact (@lem6157659 True). Qed.
Lemma lem6157661 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term464 A B f s) = True.
Proof. exact (TRANS (@lem6157657 A B f s h1) (@lem6157660)). Qed.
Lemma lem6157662 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (q' : Prop) : term471 A B C s f g op q'.
Proof. exact (@lem6157642 A B C s f g op True q'). Qed.
Lemma lem6157663 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (q' : Prop) (s : A -> Prop) (h1 : @FINITE A s) : term472 A B C s f g op q'.
Proof. exact (@lem6157662 A B C s f g op q' (@lem6157661 A B f s h1)). Qed.
Lemma lem6157720 {A B : Type'} (f : A -> B) (y : A) : (term39 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6157721 {B C : Type'} (f : B -> C) (y : B) : (term39 B C f y) = (f y).
Proof. exact (@lem6157720 B C f y). Qed.
Lemma lem6157722 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) (j : B) : (term473 A B C f g x op j) = (term439 A B C f g x op j).
Proof. exact (@lem6157721 B C (term381 A B C f g x op) j). Qed.
Lemma lem6157723 {A B C : Type'} (f : A -> B) (y : B) (g : A -> C) (x : A) (op : type1400 C) : (term439 A B C f g x op y) = (term380 A B C f y g x op).
Proof. exact (eq_refl (term439 A B C f g x op y)). Qed.
Lemma lem6157724 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) : (term474 A B C f g x op) = (term381 A B C f g x op).
Proof. exact (fun_ext (fun y : B => @lem6157723 A B C f y g x op)). Qed.
Lemma lem6157725 {B : Type'} (j : B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem6157726 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) (j : B) : (term473 A B C f g x op j) = (term439 A B C f g x op j).
Proof. exact (MK_COMB (@lem6157724 A B C f g x op) (@lem6157725 B j)). Qed.
Lemma lem6157727 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6157728 {A B C : Type'} (f : A -> B) (g : A -> C) (x : A) (op : type1400 C) (j : B) : (term475 A B C f g x op j) = (term476 A B C f g x op j).
Proof. exact (MK_COMB (@lem6157727 C) (@lem6157726 A B C f g x op j)). Qed.
Lemma lem6157729 {A B C : Type'} (f : A -> B) (j : B) (g : A -> C) (x : A) (op : type1400 C) : (term439 A B C f g x op j) = (term380 A B C f j g x op).
Proof. exact (eq_refl (term439 A B C f g x op j)). Qed.
Lemma lem6157730 {A B C : Type'} (f : A -> B) (j : B) (g : A -> C) (x : A) (op : type1400 C) : ((term473 A B C f g x op j) = (term439 A B C f g x op j)) = ((term439 A B C f g x op j) = (term380 A B C f j g x op)).
Proof. exact (MK_COMB (@lem6157728 A B C f g x op j) (@lem6157729 A B C f j g x op)). Qed.
Lemma lem6157731 {A B C : Type'} (f : A -> B) (j : B) (g : A -> C) (x : A) (op : type1400 C) : (term439 A B C f g x op j) = (term380 A B C f j g x op).
Proof. exact (EQ_MP (@lem6157730 A B C f j g x op) (@lem6157722 A B C f g x op j)). Qed.
Lemma lem6157780 {A B C : Type'} (f : A -> B) (j : B) (g : A -> C) (op : type1400 C) : (term441 A B C f g op j) = (term415 A B C f j g op).
Proof. exact (fun_ext (fun x : A => @lem6157731 A B C f j g x op)). Qed.
Lemma lem6157829 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@iterate C A op s).
Proof. exact (eq_refl (@iterate C A op s)). Qed.
Lemma lem6157830 {A B C : Type'} (s : A -> Prop) (f : A -> B) (j : B) (g : A -> C) (op : type1400 C) : (term443 A B C s f g op j) = (term417 A B C s f j g op).
Proof. exact (MK_COMB (@lem6157829 A C op s) (@lem6157780 A B C f j g op)). Qed.
Lemma lem6157879 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term445 A B C s f g op) = (term420 A B C s f g op).
Proof. exact (fun_ext (fun j : B => @lem6157830 A B C s f j g op)). Qed.
Lemma lem6157928 {A B C : Type'} (op : type1400 C) (f : A -> B) (s : A -> Prop) : (term354 A B C op f s) = (term354 A B C op f s).
Proof. exact (eq_refl (term354 A B C op f s)). Qed.
Lemma lem6157929 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term447 A B C s f g op) = (term421 A B C s f g op).
Proof. exact (MK_COMB (@lem6157928 A B C op f s) (@lem6157879 A B C s f g op)). Qed.
Lemma lem6157978 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term386 A B C s f g op) = (term386 A B C s f g op).
Proof. exact (eq_refl (term386 A B C s f g op)). Qed.
Lemma lem6157979 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : ((term384 A B C s f g op) = (term447 A B C s f g op)) = ((term384 A B C s f g op) = (term421 A B C s f g op)).
Proof. exact (MK_COMB (@lem6157978 A B C s f g op) (@lem6157929 A B C s f g op)). Qed.
Lemma lem6158078 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : term477 A B C s f g op.
Proof. exact (fun h0 : True => @lem6157979 A B C s f g op). Qed.
Lemma lem6158079 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (s : A -> Prop) (h1 : @FINITE A s) : term478 A B C s f g op.
Proof. exact (@lem6157663 A B C f g op ((term384 A B C s f g op) = (term421 A B C s f g op)) s h1). Qed.
Lemma lem6158080 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (s : A -> Prop) (h1 : @FINITE A s) : (term449 A B C s f g op) = (term479 A B C s f g op).
Proof. exact (@lem6158079 A B C f g op s h1 (@lem6158078 A B C s f g op)). Qed.
Lemma lem6158082 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem6158083 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term479 A B C s f g op) = ((term384 A B C s f g op) = (term421 A B C s f g op)).
Proof. exact (@lem6158082 ((term384 A B C s f g op) = (term421 A B C s f g op))). Qed.
Lemma lem6158182 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (s : A -> Prop) (h1 : @FINITE A s) : (term449 A B C s f g op) = ((term384 A B C s f g op) = (term421 A B C s f g op)).
Proof. exact (TRANS (@lem6158080 A B C f g op s h1) (@lem6158083 A B C s f g op)). Qed.
Lemma lem6158183 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (q' : Prop) : term480 A B C s f g op q'.
Proof. exact (@lem6157629 A B C s f g op ((term384 A B C s f g op) = (term421 A B C s f g op)) q'). Qed.
Lemma lem6158184 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (q' : Prop) (s : A -> Prop) (h1 : @FINITE A s) : term481 A B C s f g op q'.
Proof. exact (@lem6158183 A B C s f g op q' (@lem6158182 A B C f g op s h1)). Qed.
Lemma lem6158189 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : (term384 A B C s f g op) = (term421 A B C s f g op)) : (term384 A B C s f g op) = (term421 A B C s f g op).
Proof. exact (h1). Qed.
Lemma lem6158190 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : (term384 A B C s f g op) = (term421 A B C s f g op)) : (term384 A B C s f g op) = (term421 A B C s f g op).
Proof. exact (@lem6158189 A B C s f g op h1). Qed.
Lemma lem6158239 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6158240 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : (term384 A B C s f g op) = (term421 A B C s f g op)) : (term386 A B C s f g op) = (term482 A B C s f g op).
Proof. exact (MK_COMB (@lem6158239 C) (@lem6158190 A B C s f g op h1)). Qed.
Lemma lem6158337 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term421 A B C s f g op) = (term421 A B C s f g op).
Proof. exact (eq_refl (term421 A B C s f g op)). Qed.
Lemma lem6158338 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : (term384 A B C s f g op) = (term421 A B C s f g op)) : ((term384 A B C s f g op) = (term421 A B C s f g op)) = ((term421 A B C s f g op) = (term421 A B C s f g op)).
Proof. exact (MK_COMB (@lem6158240 A B C s f g op h1) (@lem6158337 A B C s f g op)). Qed.
Lemma lem6158340 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6158341 {C : Type'} (x : C) : (x = x) = True.
Proof. exact (@lem6158340 C x). Qed.
Lemma lem6158342 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : ((term421 A B C s f g op) = (term421 A B C s f g op)) = True.
Proof. exact (@lem6158341 C (term421 A B C s f g op)). Qed.
Lemma lem6158345 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term483 A B C s f g op) = (term483 A B C s f g op).
Proof. exact (eq_refl (term483 A B C s f g op)). Qed.
Lemma lem6158346 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term483 A B C s f g op) = (((term421 A B C s f g op) = (term421 A B C s f g op)) = True).
Proof. exact (eq_refl (term483 A B C s f g op)). Qed.
Lemma lem6158347 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term484 A B C s f g op) = (term484 A B C s f g op).
Proof. exact (eq_refl (term484 A B C s f g op)). Qed.
Lemma lem6158348 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : ((term483 A B C s f g op) = (term483 A B C s f g op)) = ((term483 A B C s f g op) = (((term421 A B C s f g op) = (term421 A B C s f g op)) = True)).
Proof. exact (MK_COMB (@lem6158347 A B C s f g op) (@lem6158346 A B C s f g op)). Qed.
Lemma lem6158349 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term483 A B C s f g op) = (((term421 A B C s f g op) = (term421 A B C s f g op)) = True).
Proof. exact (eq_refl (term483 A B C s f g op)). Qed.
Lemma lem6158350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6158351 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term484 A B C s f g op) = (term485 A B C s f g op).
Proof. exact (MK_COMB (@lem6158350) (@lem6158349 A B C s f g op)). Qed.
Lemma lem6158352 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (((term421 A B C s f g op) = (term421 A B C s f g op)) = True) = (((term421 A B C s f g op) = (term421 A B C s f g op)) = True).
Proof. exact (eq_refl (((term421 A B C s f g op) = (term421 A B C s f g op)) = True)). Qed.
Lemma lem6158353 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : ((term483 A B C s f g op) = (((term421 A B C s f g op) = (term421 A B C s f g op)) = True)) = ((((term421 A B C s f g op) = (term421 A B C s f g op)) = True) = (((term421 A B C s f g op) = (term421 A B C s f g op)) = True)).
Proof. exact (MK_COMB (@lem6158351 A B C s f g op) (@lem6158352 A B C s f g op)). Qed.
Lemma lem6158354 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : ((term483 A B C s f g op) = (term483 A B C s f g op)) = ((((term421 A B C s f g op) = (term421 A B C s f g op)) = True) = (((term421 A B C s f g op) = (term421 A B C s f g op)) = True)).
Proof. exact (TRANS (@lem6158348 A B C s f g op) (@lem6158353 A B C s f g op)). Qed.
Lemma lem6158355 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (((term421 A B C s f g op) = (term421 A B C s f g op)) = True) = (((term421 A B C s f g op) = (term421 A B C s f g op)) = True).
Proof. exact (EQ_MP (@lem6158354 A B C s f g op) (@lem6158345 A B C s f g op)). Qed.
Lemma lem6158356 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : ((term421 A B C s f g op) = (term421 A B C s f g op)) = True.
Proof. exact (EQ_MP (@lem6158355 A B C s f g op) (@lem6158342 A B C s f g op)). Qed.
Lemma lem6158357 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : (term384 A B C s f g op) = (term421 A B C s f g op)) : ((term384 A B C s f g op) = (term421 A B C s f g op)) = True.
Proof. exact (TRANS (@lem6158338 A B C s f g op h1) (@lem6158356 A B C s f g op)). Qed.
Lemma lem6158358 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : term486 A B C s f g op.
Proof. exact (fun h0 : (term384 A B C s f g op) = (term421 A B C s f g op) => @lem6158357 A B C s f g op h0). Qed.
Lemma lem6158359 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (s : A -> Prop) (h1 : @FINITE A s) : term487 A B C s f g op.
Proof. exact (@lem6158184 A B C f g op True s h1). Qed.
Lemma lem6158360 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (s : A -> Prop) (h1 : @FINITE A s) : (term488 A B C s f g op) = (term489 A B C s f g op).
Proof. exact (@lem6158359 A B C f g op s h1 (@lem6158358 A B C s f g op)). Qed.
Lemma lem6158364 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6158365 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) : (term489 A B C s f g op) = True.
Proof. exact (@lem6158364 ((term384 A B C s f g op) = (term421 A B C s f g op))). Qed.
Lemma lem6158366 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (s : A -> Prop) (h1 : @FINITE A s) : (term488 A B C s f g op) = True.
Proof. exact (TRANS (@lem6158360 A B C f g op s h1) (@lem6158365 A B C s f g op)). Qed.
Lemma lem6158367 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (s : A -> Prop) (h1 : @FINITE A s) : True = (term488 A B C s f g op).
Proof. exact (SYM (@lem6158366 A B C f g op s h1)). Qed.
Lemma lem6158368 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (s : A -> Prop) (h1 : @FINITE A s) : term488 A B C s f g op.
Proof. exact (EQ_MP (@lem6158367 A B C f g op s h1) (@lem0)). Qed.
Lemma lem6158369 {A B C : Type'} (f : A -> B) (g : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : @FINITE A s) (h2 : @monoidal C op) : (term384 A B C s f g op) = (term421 A B C s f g op).
Proof. exact (@lem6158368 A B C f g op s h1 (@lem6157597 A B C s f g op h2)). Qed.
Lemma lem6158370 {A B C : Type'} (f : A -> B) (g : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : @FINITE A s) (h2 : @monoidal C op) : (term321 A B C op s f g) = (term20 A B C op s f g).
Proof. exact (EQ_MP (@lem6157551 A B C s f g op h2) (@lem6158369 A B C f g s op h1 h2)). Qed.
Lemma lem6158371 {A B C : Type'} (f : A -> B) (g : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : @FINITE A s) (h2 : @monoidal C op) : term490 A B C op s f g.
Proof. exact (conj (@lem6156840 A B C f g s op h1 h2) (@lem6158370 A B C f g s op h1 h2)). Qed.
Lemma lem6158372 {A B C : Type'} (f : A -> B) (g : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : @FINITE A s) (h2 : @monoidal C op) : term491 A B C op s f g.
Proof. exact (ex_intro (term492 A B C op s f g) (term321 A B C op s f g) (@lem6158371 A B C f g s op h1 h2)). Qed.
Lemma lem6158373 {A B C : Type'} (f : A -> B) (g : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : @FINITE A s) (h2 : @monoidal C op) : (@iterate C A op s g) = (term20 A B C op s f g).
Proof. exact (@lem6155106 A B C op s f g (@lem6158372 A B C f g s op h1 h2)). Qed.
Lemma lem6158374 {A B C : Type'} (f : A -> B) (g : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : @FINITE A s) (h2 : @monoidal C op) : (@FINITE A s) = ((@iterate C A op s g) = (term20 A B C op s f g)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem6158373 A B C f g s op h1 h2) (fun h3 : (@iterate C A op s g) = (term20 A B C op s f g) => @lem6155102 A s h1)). Qed.
Lemma lem6158375 {A B C : Type'} (f : A -> B) (g : A -> C) (s : A -> Prop) (op : type1400 C) (h1 : @FINITE A s) (h2 : @monoidal C op) : (@iterate C A op s g) = (term20 A B C op s f g).
Proof. exact (EQ_MP (@lem6158374 A B C f g s op h1 h2) (@lem6155102 A s h1)). Qed.
Lemma lem6158376 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : term493 A B C op s f g.
Proof. exact (fun h0 : @FINITE A s => @lem6158375 A B C f g s op h0 h1). Qed.
Lemma lem6158381 {A B C : Type'} (f : A -> B) (g : A -> C) (op : type1400 C) (h1 : @monoidal C op) : term494 A B C op f g.
Proof. exact (fun s : A -> Prop => @lem6158376 A B C s f g op h1). Qed.
Lemma lem6158386 {A B C : Type'} (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term495 A B C op f.
Proof. exact (fun g : A -> C => @lem6158381 A B C f g op h1). Qed.
Lemma lem6158391 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term496 A B C op.
Proof. exact (fun f : A -> B => @lem6158386 A B C f op h1). Qed.
Lemma lem6158392 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = (term496 A B C op).
Proof. exact (prop_ext (fun h2 : @monoidal C op => @lem6158391 A B C op h1) (fun h2 : term496 A B C op => @lem6155101 C op h1)). Qed.
Lemma lem6158393 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term496 A B C op.
Proof. exact (EQ_MP (@lem6158392 A B C op h1) (@lem6155101 C op h1)). Qed.
Lemma lem6158394 {A B C : Type'} (op : type1400 C) : term497 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem6158393 A B C op h0). Qed.
Lemma lem6158399 {A B C : Type'} : term498 A B C.
Proof. exact (fun op : type1400 C => @lem6158394 A B C op). Qed.

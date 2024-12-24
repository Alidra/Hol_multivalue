Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_MULTICOUNT_GEN_term_abbrevs.
Require Import CARD_EQ_NSUM_spec.
Require Import CONJ_ASSOC_spec.
Require Import EQ_TRANS_spec.
Require Import FINITE_RESTRICT_spec.
Require Import MULT_CLAUSES_spec.
Require Import NSUM_CONST_spec.
Require Import NSUM_EQ_spec.
Require Import NSUM_NSUM_RESTRICT_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem6991993 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem6991994 : term1.
Proof. exact (proj2 (@lem6991993)). Qed.
Lemma lem6991995 : term2.
Proof. exact (proj2 (@lem6991994)). Qed.
Lemma lem6992011 : term3.
Proof. exact (proj1 (@lem6991995)). Qed.
Lemma lem6992012 (m : nat) : term4 m.
Proof. exact (@lem6992011 m). Qed.
Lemma lem6992013 (m : nat) : (term4 m) = ((term5 m) = m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem6992027 {_127166 : Type'} (h1 : term6 _127166) : term6 _127166.
Proof. exact (h1). Qed.
Lemma lem6992028 {_127166 : Type'} (f : _127166 -> nat) (h1 : term6 _127166) : term7 _127166 f.
Proof. exact (@lem6992027 _127166 h1 f). Qed.
Lemma lem6992029 {_127166 : Type'} (f : _127166 -> nat) : (term7 _127166 f) = (term8 _127166 f).
Proof. exact (eq_refl (term7 _127166 f)). Qed.
Lemma lem6992030 {_127166 : Type'} (f : _127166 -> nat) (h1 : term6 _127166) : term8 _127166 f.
Proof. exact (EQ_MP (@lem6992029 _127166 f) (@lem6992028 _127166 f h1)). Qed.
Lemma lem6992031 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term6 _127166) : term9 _127166 f g.
Proof. exact (@lem6992030 _127166 f h1 g). Qed.
Lemma lem6992032 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term9 _127166 f g) = (term10 _127166 f g).
Proof. exact (eq_refl (term9 _127166 f g)). Qed.
Lemma lem6992033 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term6 _127166) : term10 _127166 f g.
Proof. exact (EQ_MP (@lem6992032 _127166 f g) (@lem6992031 _127166 f g h1)). Qed.
Lemma lem6992034 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (s : _127166 -> Prop) (h1 : term6 _127166) : term11 _127166 f g s.
Proof. exact (@lem6992033 _127166 f g h1 s). Qed.
Lemma lem6992035 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term11 _127166 f g s) = (term12 _127166 f s g).
Proof. exact (eq_refl (term11 _127166 f g s)). Qed.
Lemma lem6992036 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) (h1 : term6 _127166) : term12 _127166 f s g.
Proof. exact (EQ_MP (@lem6992035 _127166 f s g) (@lem6992034 _127166 f g s h1)). Qed.
Lemma lem6992037 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term13 _127166 s f g) : term13 _127166 s f g.
Proof. exact (h1). Qed.
Lemma lem6992038 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term13 _127166 s f g) (h2 : term6 _127166) : (@nsum _127166 s f) = (@nsum _127166 s g).
Proof. exact (@lem6992036 _127166 f s g h2 (@lem6992037 _127166 s f g h1)). Qed.
Lemma lem6992039 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term13 _127166 s f g) : term14 _127166 f s g.
Proof. exact (fun h0 : term6 _127166 => @lem6992038 _127166 s f g h1 h0). Qed.
Lemma lem6992040 {_127166 : Type'} (h1 : term6 _127166) : term6 _127166.
Proof. exact (h1). Qed.
Lemma lem6992041 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term13 _127166 s f g) (h2 : term6 _127166) : (@nsum _127166 s f) = (@nsum _127166 s g).
Proof. exact (@lem6992039 _127166 s f g h1 (@lem6992040 _127166 h2)). Qed.
Lemma lem6992042 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) (h1 : term6 _127166) : term12 _127166 f s g.
Proof. exact (fun h0 : term13 _127166 s f g => @lem6992041 _127166 s f g h0 h1). Qed.
Lemma lem6992043 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (h1 : term6 _127166) : term15 _127166 f s.
Proof. exact (fun g : _127166 -> nat => @lem6992042 _127166 f s g h1). Qed.
Lemma lem6992044 {_127166 : Type'} (f : _127166 -> nat) (h1 : term6 _127166) : term16 _127166 f.
Proof. exact (fun s : _127166 -> Prop => @lem6992043 _127166 f s h1). Qed.
Lemma lem6992045 {_127166 : Type'} (h1 : term6 _127166) : term17 _127166.
Proof. exact (fun f : _127166 -> nat => @lem6992044 _127166 f h1). Qed.
Lemma lem6992046 {_127166 : Type'} : term18 _127166.
Proof. exact (fun h0 : term6 _127166 => @lem6992045 _127166 h0). Qed.
Lemma lem6992047 {_127166 : Type'} : term17 _127166.
Proof. exact (@lem6992046 _127166 (@lem6938831 _127166)). Qed.
Lemma lem6992048 {_127166 : Type'} (f : _127166 -> nat) : term19 _127166 f.
Proof. exact (@lem6992047 _127166 f). Qed.
Lemma lem6992049 {_127166 : Type'} (f : _127166 -> nat) : (term19 _127166 f) = (term16 _127166 f).
Proof. exact (eq_refl (term19 _127166 f)). Qed.
Lemma lem6992050 {_127166 : Type'} (f : _127166 -> nat) : term16 _127166 f.
Proof. exact (EQ_MP (@lem6992049 _127166 f) (@lem6992048 _127166 f)). Qed.
Lemma lem6992051 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) : term20 _127166 f s.
Proof. exact (@lem6992050 _127166 f s). Qed.
Lemma lem6992052 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) : (term20 _127166 f s) = (term15 _127166 f s).
Proof. exact (eq_refl (term20 _127166 f s)). Qed.
Lemma lem6992053 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) : term15 _127166 f s.
Proof. exact (EQ_MP (@lem6992052 _127166 f s) (@lem6992051 _127166 f s)). Qed.
Lemma lem6992054 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : term21 _127166 f s g.
Proof. exact (@lem6992053 _127166 f s g). Qed.
Lemma lem6992055 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term21 _127166 f s g) = (term12 _127166 f s g).
Proof. exact (eq_refl (term21 _127166 f s g)). Qed.
Lemma lem6992057 {_127166 : Type'} (h1 : term6 _127166) : term6 _127166.
Proof. exact (h1). Qed.
Lemma lem6992058 {_127166 : Type'} (f : _127166 -> nat) (h1 : term6 _127166) : term7 _127166 f.
Proof. exact (@lem6992057 _127166 h1 f). Qed.
Lemma lem6992059 {_127166 : Type'} (f : _127166 -> nat) : (term7 _127166 f) = (term8 _127166 f).
Proof. exact (eq_refl (term7 _127166 f)). Qed.
Lemma lem6992060 {_127166 : Type'} (f : _127166 -> nat) (h1 : term6 _127166) : term8 _127166 f.
Proof. exact (EQ_MP (@lem6992059 _127166 f) (@lem6992058 _127166 f h1)). Qed.
Lemma lem6992061 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term6 _127166) : term9 _127166 f g.
Proof. exact (@lem6992060 _127166 f h1 g). Qed.
Lemma lem6992062 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term9 _127166 f g) = (term10 _127166 f g).
Proof. exact (eq_refl (term9 _127166 f g)). Qed.
Lemma lem6992063 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term6 _127166) : term10 _127166 f g.
Proof. exact (EQ_MP (@lem6992062 _127166 f g) (@lem6992061 _127166 f g h1)). Qed.
Lemma lem6992064 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (s : _127166 -> Prop) (h1 : term6 _127166) : term11 _127166 f g s.
Proof. exact (@lem6992063 _127166 f g h1 s). Qed.
Lemma lem6992065 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term11 _127166 f g s) = (term12 _127166 f s g).
Proof. exact (eq_refl (term11 _127166 f g s)). Qed.
Lemma lem6992066 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) (h1 : term6 _127166) : term12 _127166 f s g.
Proof. exact (EQ_MP (@lem6992065 _127166 f s g) (@lem6992064 _127166 f g s h1)). Qed.
Lemma lem6992067 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term13 _127166 s f g) : term13 _127166 s f g.
Proof. exact (h1). Qed.
Lemma lem6992068 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term13 _127166 s f g) (h2 : term6 _127166) : (@nsum _127166 s f) = (@nsum _127166 s g).
Proof. exact (@lem6992066 _127166 f s g h2 (@lem6992067 _127166 s f g h1)). Qed.
Lemma lem6992069 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term13 _127166 s f g) : term14 _127166 f s g.
Proof. exact (fun h0 : term6 _127166 => @lem6992068 _127166 s f g h1 h0). Qed.
Lemma lem6992070 {_127166 : Type'} (h1 : term6 _127166) : term6 _127166.
Proof. exact (h1). Qed.
Lemma lem6992071 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term13 _127166 s f g) (h2 : term6 _127166) : (@nsum _127166 s f) = (@nsum _127166 s g).
Proof. exact (@lem6992069 _127166 s f g h1 (@lem6992070 _127166 h2)). Qed.
Lemma lem6992072 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) (h1 : term6 _127166) : term12 _127166 f s g.
Proof. exact (fun h0 : term13 _127166 s f g => @lem6992071 _127166 s f g h0 h1). Qed.
Lemma lem6992073 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (h1 : term6 _127166) : term15 _127166 f s.
Proof. exact (fun g : _127166 -> nat => @lem6992072 _127166 f s g h1). Qed.
Lemma lem6992074 {_127166 : Type'} (f : _127166 -> nat) (h1 : term6 _127166) : term16 _127166 f.
Proof. exact (fun s : _127166 -> Prop => @lem6992073 _127166 f s h1). Qed.
Lemma lem6992075 {_127166 : Type'} (h1 : term6 _127166) : term17 _127166.
Proof. exact (fun f : _127166 -> nat => @lem6992074 _127166 f h1). Qed.
Lemma lem6992076 {_127166 : Type'} : term18 _127166.
Proof. exact (fun h0 : term6 _127166 => @lem6992075 _127166 h0). Qed.
Lemma lem6992077 {_127166 : Type'} : term17 _127166.
Proof. exact (@lem6992076 _127166 (@lem6938831 _127166)). Qed.
Lemma lem6992078 {_127166 : Type'} (f : _127166 -> nat) : term19 _127166 f.
Proof. exact (@lem6992077 _127166 f). Qed.
Lemma lem6992079 {_127166 : Type'} (f : _127166 -> nat) : (term19 _127166 f) = (term16 _127166 f).
Proof. exact (eq_refl (term19 _127166 f)). Qed.
Lemma lem6992080 {_127166 : Type'} (f : _127166 -> nat) : term16 _127166 f.
Proof. exact (EQ_MP (@lem6992079 _127166 f) (@lem6992078 _127166 f)). Qed.
Lemma lem6992081 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) : term20 _127166 f s.
Proof. exact (@lem6992080 _127166 f s). Qed.
Lemma lem6992082 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) : (term20 _127166 f s) = (term15 _127166 f s).
Proof. exact (eq_refl (term20 _127166 f s)). Qed.
Lemma lem6992083 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) : term15 _127166 f s.
Proof. exact (EQ_MP (@lem6992082 _127166 f s) (@lem6992081 _127166 f s)). Qed.
Lemma lem6992084 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : term21 _127166 f s g.
Proof. exact (@lem6992083 _127166 f s g). Qed.
Lemma lem6992085 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term21 _127166 f s g) = (term12 _127166 f s g).
Proof. exact (eq_refl (term21 _127166 f s g)). Qed.
Lemma lem6992087 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem6992088 {A : Type'} (x : A) (h1 : term22 A) : term23 A x.
Proof. exact (@lem6992087 A h1 x). Qed.
Lemma lem6992089 {A : Type'} (x : A) : (term23 A x) = (term24 A x).
Proof. exact (eq_refl (term23 A x)). Qed.
Lemma lem6992090 {A : Type'} (x : A) (h1 : term22 A) : term24 A x.
Proof. exact (EQ_MP (@lem6992089 A x) (@lem6992088 A x h1)). Qed.
Lemma lem6992091 {A : Type'} (x : A) (y : A) (h1 : term22 A) : term25 A x y.
Proof. exact (@lem6992090 A x h1 y). Qed.
Lemma lem6992092 {A : Type'} (y : A) (x : A) : (term25 A x y) = (term26 A y x).
Proof. exact (eq_refl (term25 A x y)). Qed.
Lemma lem6992093 {A : Type'} (y : A) (x : A) (h1 : term22 A) : term26 A y x.
Proof. exact (EQ_MP (@lem6992092 A y x) (@lem6992091 A x y h1)). Qed.
Lemma lem6992094 {A : Type'} (y : A) (x : A) (z : A) (h1 : term22 A) : term27 A y x z.
Proof. exact (@lem6992093 A y x h1 z). Qed.
Lemma lem6992095 {A : Type'} (y : A) (x : A) (z : A) : (term27 A y x z) = (term28 A y x z).
Proof. exact (eq_refl (term27 A y x z)). Qed.
Lemma lem6992096 {A : Type'} (y : A) (x : A) (z : A) (h1 : term22 A) : term28 A y x z.
Proof. exact (EQ_MP (@lem6992095 A y x z) (@lem6992094 A y x z h1)). Qed.
Lemma lem6992097 {A : Type'} (x : A) (y : A) (z : A) (h1 : term29 A x y z) : term29 A x y z.
Proof. exact (h1). Qed.
Lemma lem6992098 {A : Type'} (x : A) (y : A) (z : A) (h1 : term22 A) (h2 : term29 A x y z) : x = z.
Proof. exact (@lem6992096 A y x z h1 (@lem6992097 A x y z h2)). Qed.
Lemma lem6992099 {A : Type'} (x : A) (y : A) (z : A) (h1 : term29 A x y z) : term30 A x z.
Proof. exact (fun h0 : term22 A => @lem6992098 A x y z h0 h1). Qed.
Lemma lem6992100 {A : Type'} (x : A) (z : A) (h1 : term31 A x z) : term31 A x z.
Proof. exact (h1). Qed.
Lemma lem6992101 {A : Type'} (x : A) (z : A) (h1 : term31 A x z) : term30 A x z.
Proof. exact (ex_elim (@lem6992100 A x z h1) (fun y : A => fun h0 : term32 A x z y => @lem6992099 A x y z h0)). Qed.
Lemma lem6992102 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem6992103 {A : Type'} (x : A) (z : A) (h1 : term22 A) (h2 : term31 A x z) : x = z.
Proof. exact (@lem6992101 A x z h2 (@lem6992102 A h1)). Qed.
Lemma lem6992104 {A : Type'} (x : A) (z : A) (h1 : term22 A) : term33 A x z.
Proof. exact (fun h0 : term31 A x z => @lem6992103 A x z h1 h0). Qed.
Lemma lem6992105 {A : Type'} (x : A) (h1 : term22 A) : term34 A x.
Proof. exact (fun z : A => @lem6992104 A x z h1). Qed.
Lemma lem6992106 {A : Type'} (h1 : term22 A) : term35 A.
Proof. exact (fun x : A => @lem6992105 A x h1). Qed.
Lemma lem6992107 {A : Type'} : term36 A.
Proof. exact (fun h0 : term22 A => @lem6992106 A h0). Qed.
Lemma lem6992108 {A : Type'} : term35 A.
Proof. exact (@lem6992107 A (@lem403 A)). Qed.
Lemma lem6992109 {A : Type'} (x : A) : term37 A x.
Proof. exact (@lem6992108 A x). Qed.
Lemma lem6992110 {A : Type'} (x : A) : (term37 A x) = (term34 A x).
Proof. exact (eq_refl (term37 A x)). Qed.
Lemma lem6992111 {A : Type'} (x : A) : term34 A x.
Proof. exact (EQ_MP (@lem6992110 A x) (@lem6992109 A x)). Qed.
Lemma lem6992112 {A : Type'} (x : A) (z : A) : term38 A x z.
Proof. exact (@lem6992111 A x z). Qed.
Lemma lem6992113 {A : Type'} (x : A) (z : A) : (term38 A x z) = (term33 A x z).
Proof. exact (eq_refl (term38 A x z)). Qed.
Lemma lem6992115 (t1 : Prop) : term39 t1.
Proof. exact (@lem512 t1). Qed.
Lemma lem6992116 (t1 : Prop) : (term39 t1) = (term40 t1).
Proof. exact (eq_refl (term39 t1)). Qed.
Lemma lem6992117 (t1 : Prop) : term40 t1.
Proof. exact (EQ_MP (@lem6992116 t1) (@lem6992115 t1)). Qed.
Lemma lem6992118 (t1 : Prop) (t2 : Prop) : term41 t1 t2.
Proof. exact (@lem6992117 t1 t2). Qed.
Lemma lem6992119 (t1 : Prop) (t2 : Prop) : (term41 t1 t2) = (term42 t1 t2).
Proof. exact (eq_refl (term41 t1 t2)). Qed.
Lemma lem6992120 (t1 : Prop) (t2 : Prop) : term42 t1 t2.
Proof. exact (EQ_MP (@lem6992119 t1 t2) (@lem6992118 t1 t2)). Qed.
Lemma lem6992121 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term43 t1 t2 t3.
Proof. exact (@lem6992120 t1 t2 t3). Qed.
Lemma lem6992122 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term43 t1 t2 t3) = ((term44 t1 t2 t3) = (term45 t1 t2 t3)).
Proof. exact (eq_refl (term43 t1 t2 t3)). Qed.
Lemma lem6992127 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term44 t1 t2 t3) = (term45 t1 t2 t3).
Proof. exact (EQ_MP (@lem6992122 t1 t2 t3) (@lem6992121 t1 t2 t3)). Qed.
Lemma lem6992128 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) : (term46 A B t s R k) = (term47 A B t s R k).
Proof. exact (@lem6992127 (@FINITE A s) (@FINITE B t) (term48 A B t s R k)). Qed.
Lemma lem6992147 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6992148 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) : (term49 A B t s R k) = (term50 A B t s R k).
Proof. exact (MK_COMB (@lem6992147) (@lem6992128 A B t s R k)). Qed.
Lemma lem6992157 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : ((term51 A B s t R) = (term52 B t k)) = ((term51 A B s t R) = (term52 B t k)).
Proof. exact (eq_refl ((term51 A B s t R) = (term52 B t k))). Qed.
Lemma lem6992158 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : (term53 A B s R t k) = (term54 A B s R t k).
Proof. exact (MK_COMB (@lem6992148 A B t s R k) (@lem6992157 A B s R t k)). Qed.
Lemma lem6992161 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : (term54 A B s R t k) = (term53 A B s R t k).
Proof. exact (SYM (@lem6992158 A B s R t k)). Qed.
Lemma lem6992162 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term47 A B t s R k) : term47 A B t s R k.
Proof. exact (h1). Qed.
Lemma lem6992163 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term48 A B t s R k) : term48 A B t s R k.
Proof. exact (h1). Qed.
Lemma lem6992164 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : term55 A B s t.
Proof. exact (h1). Qed.
Lemma lem6992166 {A : Type'} (x : A) (z : A) : term33 A x z.
Proof. exact (EQ_MP (@lem6992113 A x z) (@lem6992112 A x z)). Qed.
Lemma lem6992167 (x : nat) (z : nat) : term56 x z.
Proof. exact (@lem6992166 nat x z). Qed.
Lemma lem6992168 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term57 A B s R t k.
Proof. exact (@lem6992167 (term51 A B s t R) (term52 B t k)). Qed.
Lemma lem6992170 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : term12 _127166 f s g.
Proof. exact (EQ_MP (@lem6992085 _127166 f s g) (@lem6992084 _127166 f s g)). Qed.
Lemma lem6992171 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term12 A f s g.
Proof. exact (@lem6992170 A f s g). Qed.
Lemma lem6992172 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : term58 A B s t R.
Proof. exact (@lem6992171 A (term59 A B t R) s (term60 A B t R)). Qed.
Lemma lem6992193 {A B : Type'} (f : A -> B) (y : A) : (term61 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6992194 {A : Type'} (f : A -> nat) (y : A) : (term62 A f y) = (f y).
Proof. exact (@lem6992193 A nat f y). Qed.
Lemma lem6992195 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term63 A B t R x) = (term64 A B t R x).
Proof. exact (@lem6992194 A (term59 A B t R) x). Qed.
Lemma lem6992196 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (i : A) : (term64 A B t R i) = (term65 A B t R i).
Proof. exact (eq_refl (term64 A B t R i)). Qed.
Lemma lem6992197 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term66 A B t R) = (term59 A B t R).
Proof. exact (fun_ext (fun i : A => @lem6992196 A B t R i)). Qed.
Lemma lem6992198 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6992199 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term63 A B t R x) = (term64 A B t R x).
Proof. exact (MK_COMB (@lem6992197 A B t R) (@lem6992198 A x)). Qed.
Lemma lem6992200 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6992201 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term67 A B t R x) = (term68 A B t R x).
Proof. exact (MK_COMB (@lem6992200) (@lem6992199 A B t R x)). Qed.
Lemma lem6992202 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term64 A B t R x) = (term65 A B t R x).
Proof. exact (eq_refl (term64 A B t R x)). Qed.
Lemma lem6992203 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term63 A B t R x) = (term64 A B t R x)) = ((term64 A B t R x) = (term65 A B t R x)).
Proof. exact (MK_COMB (@lem6992201 A B t R x) (@lem6992202 A B t R x)). Qed.
Lemma lem6992204 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term64 A B t R x) = (term65 A B t R x).
Proof. exact (EQ_MP (@lem6992203 A B t R x) (@lem6992195 A B t R x)). Qed.
Lemma lem6992211 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6992212 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term68 A B t R x) = (term69 A B t R x).
Proof. exact (MK_COMB (@lem6992211) (@lem6992204 A B t R x)). Qed.
Lemma lem6992214 {A B : Type'} (f : A -> B) (y : A) : (term61 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6992215 {A : Type'} (f : A -> nat) (y : A) : (term62 A f y) = (f y).
Proof. exact (@lem6992214 A nat f y). Qed.
Lemma lem6992216 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term70 A B t R x) = (term71 A B t R x).
Proof. exact (@lem6992215 A (term60 A B t R) x). Qed.
Lemma lem6992217 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (i : A) : (term71 A B t R i) = (term72 A B t R i).
Proof. exact (eq_refl (term71 A B t R i)). Qed.
Lemma lem6992218 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term73 A B t R) = (term60 A B t R).
Proof. exact (fun_ext (fun i : A => @lem6992217 A B t R i)). Qed.
Lemma lem6992219 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6992220 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term70 A B t R x) = (term71 A B t R x).
Proof. exact (MK_COMB (@lem6992218 A B t R) (@lem6992219 A x)). Qed.
Lemma lem6992221 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6992222 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term74 A B t R x) = (term75 A B t R x).
Proof. exact (MK_COMB (@lem6992221) (@lem6992220 A B t R x)). Qed.
Lemma lem6992223 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (eq_refl (term71 A B t R x)). Qed.
Lemma lem6992224 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term70 A B t R x) = (term71 A B t R x)) = ((term71 A B t R x) = (term72 A B t R x)).
Proof. exact (MK_COMB (@lem6992222 A B t R x) (@lem6992223 A B t R x)). Qed.
Lemma lem6992225 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term71 A B t R x) = (term72 A B t R x).
Proof. exact (EQ_MP (@lem6992224 A B t R x) (@lem6992216 A B t R x)). Qed.
Lemma lem6992232 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term64 A B t R x) = (term71 A B t R x)) = ((term65 A B t R x) = (term72 A B t R x)).
Proof. exact (MK_COMB (@lem6992212 A B t R x) (@lem6992225 A B t R x)). Qed.
Lemma lem6992235 {A : Type'} (x : A) (s : A -> Prop) : (term76 A x s) = (term76 A x s).
Proof. exact (eq_refl (term76 A x s)). Qed.
Lemma lem6992236 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) (x : A) : (term77 A B s t R x) = (term78 A B s t R x).
Proof. exact (MK_COMB (@lem6992235 A x s) (@lem6992232 A B t R x)). Qed.
Lemma lem6992239 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term79 A B s t R) = (term80 A B s t R).
Proof. exact (fun_ext (fun x : A => @lem6992236 A B s t R x)). Qed.
Lemma lem6992240 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6992241 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term81 A B s t R) = (term82 A B s t R).
Proof. exact (MK_COMB (@lem6992240 A) (@lem6992239 A B s t R)). Qed.
Lemma lem6992246 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term82 A B s t R) = (term81 A B s t R).
Proof. exact (SYM (@lem6992241 A B s t R)). Qed.
Lemma lem6992248 {A : Type'} (s : A -> Prop) : term83 A s.
Proof. exact (@lem3603906 A s). Qed.
Lemma lem6992249 {A : Type'} (s : A -> Prop) : (term83 A s) = (term84 A s).
Proof. exact (eq_refl (term83 A s)). Qed.
Lemma lem6992250 {A : Type'} (s : A -> Prop) : term84 A s.
Proof. exact (EQ_MP (@lem6992249 A s) (@lem6992248 A s)). Qed.
Lemma lem6992251 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term85 A s P.
Proof. exact (@lem6992250 A s P). Qed.
Lemma lem6992252 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term85 A s P) = (term86 A s P).
Proof. exact (eq_refl (term85 A s P)). Qed.
Lemma lem6992253 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term86 A s P.
Proof. exact (EQ_MP (@lem6992252 A s P) (@lem6992251 A s P)). Qed.
Lemma lem6992254 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6992255 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term87 A s P.
Proof. exact (@lem6992253 A s P (@lem6992254 A s h1)). Qed.
Lemma lem6992256 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term87 A s P) = ((term87 A s P) = True).
Proof. exact (@lem7 (term87 A s P)). Qed.
Lemma lem6992257 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term87 A s P) = True.
Proof. exact (EQ_MP (@lem6992256 A s P) (@lem6992255 A P s h1)). Qed.
Lemma lem6992263 {_128422 : Type'} (s : _128422 -> Prop) : term88 _128422 s.
Proof. exact (@lem6991992 _128422 s). Qed.
Lemma lem6992264 {_128422 : Type'} (s : _128422 -> Prop) : (term88 _128422 s) = (term89 _128422 s).
Proof. exact (eq_refl (term88 _128422 s)). Qed.
Lemma lem6992265 {_128422 : Type'} (s : _128422 -> Prop) : term89 _128422 s.
Proof. exact (EQ_MP (@lem6992264 _128422 s) (@lem6992263 _128422 s)). Qed.
Lemma lem6992266 {_128422 : Type'} (s : _128422 -> Prop) (h1 : @FINITE _128422 s) : @FINITE _128422 s.
Proof. exact (h1). Qed.
Lemma lem6992267 {_128422 : Type'} (s : _128422 -> Prop) (h1 : @FINITE _128422 s) : (@CARD _128422 s) = (term90 _128422 s).
Proof. exact (@lem6992265 _128422 s (@lem6992266 _128422 s h1)). Qed.
Lemma lem6992273 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : @FINITE B t.
Proof. exact (proj2 (@lem6992164 A B s t h1)). Qed.
Lemma lem6992274 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem6992294 {_128422 : Type'} (s : _128422 -> Prop) : term89 _128422 s.
Proof. exact (fun h0 : @FINITE _128422 s => @lem6992267 _128422 s h0). Qed.
Lemma lem6992295 {B : Type'} (s : B -> Prop) : term89 B s.
Proof. exact (@lem6992294 B s). Qed.
Lemma lem6992296 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term91 A B t R x.
Proof. exact (@lem6992295 B (term92 A B t R x)). Qed.
Lemma lem6992298 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term93 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem6992257 A P s h0). Qed.
Lemma lem6992299 {B : Type'} (s : B -> Prop) (P : B -> Prop) : term93 B s P.
Proof. exact (@lem6992298 B s P). Qed.
Lemma lem6992300 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term94 A B t R x.
Proof. exact (@lem6992299 B t (term95 A B R x)). Qed.
Lemma lem6992301 {A B : Type'} (R : type1413 A B) (x : A) (j : B) : (term96 A B R x j) = (R x j).
Proof. exact (eq_refl (term96 A B R x j)). Qed.
Lemma lem6992302 {B : Type'} (j : B) (t : B -> Prop) : (term97 B j t) = (term97 B j t).
Proof. exact (eq_refl (term97 B j t)). Qed.
Lemma lem6992303 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) (j : B) : (term98 A B t R x j) = (term99 A B t R x j).
Proof. exact (MK_COMB (@lem6992302 B j t) (@lem6992301 A B R x j)). Qed.
Lemma lem6992304 {B : Type'} (GEN_PVAR_292 : B) : (@SETSPEC B GEN_PVAR_292) = (@SETSPEC B GEN_PVAR_292).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_292)). Qed.
Lemma lem6992305 {A B : Type'} (GEN_PVAR_292 : B) (t : B -> Prop) (R : type1413 A B) (x : A) (j : B) : (term100 A B GEN_PVAR_292 t R x j) = (term101 A B GEN_PVAR_292 t R x j).
Proof. exact (MK_COMB (@lem6992304 B GEN_PVAR_292) (@lem6992303 A B t R x j)). Qed.
Lemma lem6992306 {B : Type'} (j : B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem6992307 {A B : Type'} (GEN_PVAR_292 : B) (t : B -> Prop) (R : type1413 A B) (x : A) (j : B) : (term102 A B GEN_PVAR_292 t R x j) = (term103 A B GEN_PVAR_292 t R x j).
Proof. exact (MK_COMB (@lem6992305 A B GEN_PVAR_292 t R x j) (@lem6992306 B j)). Qed.
Lemma lem6992308 {A B : Type'} (GEN_PVAR_292 : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term104 A B GEN_PVAR_292 t R x) = (term105 A B GEN_PVAR_292 t R x).
Proof. exact (fun_ext (fun j : B => @lem6992307 A B GEN_PVAR_292 t R x j)). Qed.
Lemma lem6992309 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem6992310 {A B : Type'} (GEN_PVAR_292 : B) (t : B -> Prop) (R : type1413 A B) (x : A) : (term106 A B GEN_PVAR_292 t R x) = (term107 A B GEN_PVAR_292 t R x).
Proof. exact (MK_COMB (@lem6992309 B) (@lem6992308 A B GEN_PVAR_292 t R x)). Qed.
Lemma lem6992311 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term108 A B t R x) = (term109 A B t R x).
Proof. exact (fun_ext (fun GEN_PVAR_292 : B => @lem6992310 A B GEN_PVAR_292 t R x)). Qed.
Lemma lem6992312 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem6992313 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term110 A B t R x) = (term92 A B t R x).
Proof. exact (MK_COMB (@lem6992312 B) (@lem6992311 A B t R x)). Qed.
Lemma lem6992314 {B : Type'} : (@FINITE B) = (@FINITE B).
Proof. exact (eq_refl (@FINITE B)). Qed.
Lemma lem6992315 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term111 A B t R x) = (term112 A B t R x).
Proof. exact (MK_COMB (@lem6992314 B) (@lem6992313 A B t R x)). Qed.
Lemma lem6992316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6992317 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term113 A B t R x) = (term114 A B t R x).
Proof. exact (MK_COMB (@lem6992316) (@lem6992315 A B t R x)). Qed.
Lemma lem6992318 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem6992319 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term111 A B t R x) = True) = ((term112 A B t R x) = True).
Proof. exact (MK_COMB (@lem6992317 A B t R x) (@lem6992318)). Qed.
Lemma lem6992320 {B : Type'} (t : B -> Prop) : (term115 B t) = (term115 B t).
Proof. exact (eq_refl (term115 B t)). Qed.
Lemma lem6992321 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term94 A B t R x) = (term116 A B t R x).
Proof. exact (MK_COMB (@lem6992320 B t) (@lem6992319 A B t R x)). Qed.
Lemma lem6992322 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : term116 A B t R x.
Proof. exact (EQ_MP (@lem6992321 A B t R x) (@lem6992300 A B t R x)). Qed.
Lemma lem6992324 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem6992274 B t) (@lem6992273 A B s t h1)). Qed.
Lemma lem6992325 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : True = (@FINITE B t).
Proof. exact (SYM (@lem6992324 A B s t h1)). Qed.
Lemma lem6992326 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : @FINITE B t.
Proof. exact (EQ_MP (@lem6992325 A B s t h1) (@lem0)). Qed.
Lemma lem6992327 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (term112 A B t R x) = True.
Proof. exact (@lem6992322 A B t R x (@lem6992326 A B s t h1)). Qed.
Lemma lem6992328 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : True = (term112 A B t R x).
Proof. exact (SYM (@lem6992327 A B R x s t h1)). Qed.
Lemma lem6992329 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : term112 A B t R x.
Proof. exact (EQ_MP (@lem6992328 A B R x s t h1) (@lem0)). Qed.
Lemma lem6992330 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (term65 A B t R x) = (term72 A B t R x).
Proof. exact (@lem6992296 A B t R x (@lem6992329 A B R x s t h1)). Qed.
Lemma lem6992337 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6992338 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (term69 A B t R x) = (term117 A B t R x).
Proof. exact (MK_COMB (@lem6992337) (@lem6992330 A B R x s t h1)). Qed.
Lemma lem6992351 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term72 A B t R x) = (term72 A B t R x).
Proof. exact (eq_refl (term72 A B t R x)). Qed.
Lemma lem6992352 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : ((term65 A B t R x) = (term72 A B t R x)) = ((term72 A B t R x) = (term72 A B t R x)).
Proof. exact (MK_COMB (@lem6992338 A B R x s t h1) (@lem6992351 A B t R x)). Qed.
Lemma lem6992354 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6992355 (x : nat) : (x = x) = True.
Proof. exact (@lem6992354 nat x). Qed.
Lemma lem6992356 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term72 A B t R x) = (term72 A B t R x)) = True.
Proof. exact (@lem6992355 (term72 A B t R x)). Qed.
Lemma lem6992359 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term118 A B t R x) = (term118 A B t R x).
Proof. exact (eq_refl (term118 A B t R x)). Qed.
Lemma lem6992360 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term118 A B t R x) = (((term72 A B t R x) = (term72 A B t R x)) = True).
Proof. exact (eq_refl (term118 A B t R x)). Qed.
Lemma lem6992361 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term119 A B t R x) = (term119 A B t R x).
Proof. exact (eq_refl (term119 A B t R x)). Qed.
Lemma lem6992362 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term118 A B t R x) = (term118 A B t R x)) = ((term118 A B t R x) = (((term72 A B t R x) = (term72 A B t R x)) = True)).
Proof. exact (MK_COMB (@lem6992361 A B t R x) (@lem6992360 A B t R x)). Qed.
Lemma lem6992363 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term118 A B t R x) = (((term72 A B t R x) = (term72 A B t R x)) = True).
Proof. exact (eq_refl (term118 A B t R x)). Qed.
Lemma lem6992364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6992365 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (term119 A B t R x) = (term120 A B t R x).
Proof. exact (MK_COMB (@lem6992364) (@lem6992363 A B t R x)). Qed.
Lemma lem6992366 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (((term72 A B t R x) = (term72 A B t R x)) = True) = (((term72 A B t R x) = (term72 A B t R x)) = True).
Proof. exact (eq_refl (((term72 A B t R x) = (term72 A B t R x)) = True)). Qed.
Lemma lem6992367 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term118 A B t R x) = (((term72 A B t R x) = (term72 A B t R x)) = True)) = ((((term72 A B t R x) = (term72 A B t R x)) = True) = (((term72 A B t R x) = (term72 A B t R x)) = True)).
Proof. exact (MK_COMB (@lem6992365 A B t R x) (@lem6992366 A B t R x)). Qed.
Lemma lem6992368 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term118 A B t R x) = (term118 A B t R x)) = ((((term72 A B t R x) = (term72 A B t R x)) = True) = (((term72 A B t R x) = (term72 A B t R x)) = True)).
Proof. exact (TRANS (@lem6992362 A B t R x) (@lem6992367 A B t R x)). Qed.
Lemma lem6992369 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : (((term72 A B t R x) = (term72 A B t R x)) = True) = (((term72 A B t R x) = (term72 A B t R x)) = True).
Proof. exact (EQ_MP (@lem6992368 A B t R x) (@lem6992359 A B t R x)). Qed.
Lemma lem6992370 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (x : A) : ((term72 A B t R x) = (term72 A B t R x)) = True.
Proof. exact (EQ_MP (@lem6992369 A B t R x) (@lem6992356 A B t R x)). Qed.
Lemma lem6992371 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : ((term65 A B t R x) = (term72 A B t R x)) = True.
Proof. exact (TRANS (@lem6992352 A B R x s t h1) (@lem6992370 A B t R x)). Qed.
Lemma lem6992372 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : True = ((term65 A B t R x) = (term72 A B t R x)).
Proof. exact (SYM (@lem6992371 A B R x s t h1)). Qed.
Lemma lem6992373 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (term65 A B t R x) = (term72 A B t R x).
Proof. exact (EQ_MP (@lem6992372 A B R x s t h1) (@lem0)). Qed.
Lemma lem6992374 {A B : Type'} (R : type1413 A B) (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : term78 A B s t R x.
Proof. exact (fun h0 : @IN A x s => @lem6992373 A B R x s t h1). Qed.
Lemma lem6992379 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : term82 A B s t R.
Proof. exact (fun x : A => @lem6992374 A B R x s t h1). Qed.
Lemma lem6992380 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : term81 A B s t R.
Proof. exact (EQ_MP (@lem6992246 A B s t R) (@lem6992379 A B R s t h1)). Qed.
Lemma lem6992381 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (term51 A B s t R) = (term121 A B s t R).
Proof. exact (@lem6992172 A B s t R (@lem6992380 A B R s t h1)). Qed.
Lemma lem6992412 {_128402 _128403 : Type'} (h1 : term122 _128402 _128403) : term122 _128402 _128403.
Proof. exact (h1). Qed.
Lemma lem6992413 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (h1 : term122 _128402 _128403) : term123 _128402 _128403 R.
Proof. exact (@lem6992412 _128402 _128403 h1 R). Qed.
Lemma lem6992414 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) : (term123 _128402 _128403 R) = (term124 _128402 _128403 R).
Proof. exact (eq_refl (term123 _128402 _128403 R)). Qed.
Lemma lem6992415 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (h1 : term122 _128402 _128403) : term124 _128402 _128403 R.
Proof. exact (EQ_MP (@lem6992414 _128402 _128403 R) (@lem6992413 _128402 _128403 R h1)). Qed.
Lemma lem6992416 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (h1 : term122 _128402 _128403) : term125 _128402 _128403 R f.
Proof. exact (@lem6992415 _128402 _128403 R h1 f). Qed.
Lemma lem6992417 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term125 _128402 _128403 R f) = (term126 _128402 _128403 R f).
Proof. exact (eq_refl (term125 _128402 _128403 R f)). Qed.
Lemma lem6992418 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (h1 : term122 _128402 _128403) : term126 _128402 _128403 R f.
Proof. exact (EQ_MP (@lem6992417 _128402 _128403 R f) (@lem6992416 _128402 _128403 R f h1)). Qed.
Lemma lem6992419 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (s : _128403 -> Prop) (h1 : term122 _128402 _128403) : term127 _128402 _128403 R f s.
Proof. exact (@lem6992418 _128402 _128403 R f h1 s). Qed.
Lemma lem6992420 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term127 _128402 _128403 R f s) = (term128 _128402 _128403 s R f).
Proof. exact (eq_refl (term127 _128402 _128403 R f s)). Qed.
Lemma lem6992421 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (h1 : term122 _128402 _128403) : term128 _128402 _128403 s R f.
Proof. exact (EQ_MP (@lem6992420 _128402 _128403 s R f) (@lem6992419 _128402 _128403 R f s h1)). Qed.
Lemma lem6992422 {_128402 _128403 : Type'} (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (t : _128402 -> Prop) (h1 : term122 _128402 _128403) : term129 _128402 _128403 s R f t.
Proof. exact (@lem6992421 _128402 _128403 s R f h1 t). Qed.
Lemma lem6992423 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) : (term129 _128402 _128403 s R f t) = (term130 _128402 _128403 t s R f).
Proof. exact (eq_refl (term129 _128402 _128403 s R f t)). Qed.
Lemma lem6992424 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (h1 : term122 _128402 _128403) : term130 _128402 _128403 t s R f.
Proof. exact (EQ_MP (@lem6992423 _128402 _128403 t s R f) (@lem6992422 _128402 _128403 s R f t h1)). Qed.
Lemma lem6992425 {_128402 _128403 : Type'} (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term131 _128402 _128403 s t) : term131 _128402 _128403 s t.
Proof. exact (h1). Qed.
Lemma lem6992426 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (f : type1471 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term122 _128402 _128403) (h2 : term131 _128402 _128403 s t) : (term132 _128402 _128403 s t R f) = (term133 _128402 _128403 t s R f).
Proof. exact (@lem6992424 _128402 _128403 t s R f h1 (@lem6992425 _128402 _128403 s t h2)). Qed.
Lemma lem6992427 {_128402 _128403 : Type'} (R : type1470 _128402 _128403) (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term122 _128402 _128403) (h2 : term131 _128402 _128403 s t) : term134 _128402 _128403 t s R.
Proof. exact (fun f : type1471 _128402 _128403 => @lem6992426 _128402 _128403 R f s t h1 h2). Qed.
Lemma lem6992428 {_128402 _128403 : Type'} (s : _128403 -> Prop) (t : _128402 -> Prop) (h1 : term122 _128402 _128403) (h2 : term131 _128402 _128403 s t) : term135 _128402 _128403 t s.
Proof. exact (fun R : type1470 _128402 _128403 => @lem6992427 _128402 _128403 R s t h1 h2). Qed.
Lemma lem6992429 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) (h1 : term122 _128402 _128403) : term136 _128402 _128403 t s.
Proof. exact (fun h0 : term131 _128402 _128403 s t => @lem6992428 _128402 _128403 s t h1 h0). Qed.
Lemma lem6992430 {_128402 _128403 : Type'} (s : _128403 -> Prop) (h1 : term122 _128402 _128403) : term137 _128402 _128403 s.
Proof. exact (fun t : _128402 -> Prop => @lem6992429 _128402 _128403 t s h1). Qed.
Lemma lem6992431 {_128402 _128403 : Type'} (h1 : term122 _128402 _128403) : term138 _128402 _128403.
Proof. exact (fun s : _128403 -> Prop => @lem6992430 _128402 _128403 s h1). Qed.
Lemma lem6992432 {_128402 _128403 : Type'} : term139 _128402 _128403.
Proof. exact (fun h0 : term122 _128402 _128403 => @lem6992431 _128402 _128403 h0). Qed.
Lemma lem6992433 {_128402 _128403 : Type'} : term138 _128402 _128403.
Proof. exact (@lem6992432 _128402 _128403 (@lem6991883 _128402 _128403)). Qed.
Lemma lem6992434 {_128402 _128403 : Type'} (s : _128403 -> Prop) : term140 _128402 _128403 s.
Proof. exact (@lem6992433 _128402 _128403 s). Qed.
Lemma lem6992435 {_128402 _128403 : Type'} (s : _128403 -> Prop) : (term140 _128402 _128403 s) = (term137 _128402 _128403 s).
Proof. exact (eq_refl (term140 _128402 _128403 s)). Qed.
Lemma lem6992436 {_128402 _128403 : Type'} (s : _128403 -> Prop) : term137 _128402 _128403 s.
Proof. exact (EQ_MP (@lem6992435 _128402 _128403 s) (@lem6992434 _128402 _128403 s)). Qed.
Lemma lem6992437 {_128402 _128403 : Type'} (s : _128403 -> Prop) (t : _128402 -> Prop) : term141 _128402 _128403 s t.
Proof. exact (@lem6992436 _128402 _128403 s t). Qed.
Lemma lem6992438 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) : (term141 _128402 _128403 s t) = (term136 _128402 _128403 t s).
Proof. exact (eq_refl (term141 _128402 _128403 s t)). Qed.
Lemma lem6992441 {_128402 _128403 : Type'} (t : _128402 -> Prop) (s : _128403 -> Prop) : term136 _128402 _128403 t s.
Proof. exact (EQ_MP (@lem6992438 _128402 _128403 t s) (@lem6992437 _128402 _128403 s t)). Qed.
Lemma lem6992442 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term142 A B t s.
Proof. exact (@lem6992441 B A t s). Qed.
Lemma lem6992443 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : term143 A B t s.
Proof. exact (@lem6992442 A B t s (@lem6992164 A B s t h1)). Qed.
Lemma lem6992444 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : term144 A B t s R.
Proof. exact (@lem6992443 A B s t h1 R). Qed.
Lemma lem6992445 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) : (term144 A B t s R) = (term145 A B t s R).
Proof. exact (eq_refl (term144 A B t s R)). Qed.
Lemma lem6992446 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : term145 A B t s R.
Proof. exact (EQ_MP (@lem6992445 A B t s R) (@lem6992444 A B R s t h1)). Qed.
Lemma lem6992447 {A B : Type'} (R : type1413 A B) (f : type1415 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : term146 A B t s R f.
Proof. exact (@lem6992446 A B R s t h1 f). Qed.
Lemma lem6992448 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (f : type1415 A B) : (term146 A B t s R f) = ((term147 A B s t R f) = (term148 A B t s R f)).
Proof. exact (eq_refl (term146 A B t s R f)). Qed.
Lemma lem6992453 {A B : Type'} (R : type1413 A B) (f : type1415 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (term147 A B s t R f) = (term148 A B t s R f).
Proof. exact (EQ_MP (@lem6992448 A B t s R f) (@lem6992447 A B R f s t h1)). Qed.
Lemma lem6992454 {A B : Type'} (R : type1413 A B) (f : type1415 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (term147 A B s t R f) = (term148 A B t s R f).
Proof. exact (@lem6992453 A B R f s t h1). Qed.
Lemma lem6992455 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (term149 A B s t R) = (term150 A B t s R).
Proof. exact (@lem6992454 A B R (term151 A B) s t h1). Qed.
Lemma lem6992456 {A B : Type'} (i : A) : (term152 A B i) = (term153 B).
Proof. exact (eq_refl (term152 A B i)). Qed.
Lemma lem6992457 {B : Type'} (j : B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem6992458 {A B : Type'} (i : A) (j : B) : (term154 A B i j) = (term155 B j).
Proof. exact (MK_COMB (@lem6992456 A B i) (@lem6992457 B j)). Qed.
Lemma lem6992459 {B : Type'} (j : B) : (term155 B j) = term156.
Proof. exact (eq_refl (term155 B j)). Qed.
Lemma lem6992460 {A B : Type'} (i : A) (j : B) : (term154 A B i j) = term156.
Proof. exact (TRANS (@lem6992458 A B i j) (@lem6992459 B j)). Qed.
Lemma lem6992461 {A B : Type'} (i : A) : (term157 A B i) = (term153 B).
Proof. exact (fun_ext (fun j : B => @lem6992460 A B i j)). Qed.
Lemma lem6992462 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (i : A) : (term158 A B t R i) = (term158 A B t R i).
Proof. exact (eq_refl (term158 A B t R i)). Qed.
Lemma lem6992463 {A B : Type'} (t : B -> Prop) (R : type1413 A B) (i : A) : (term159 A B t R i) = (term72 A B t R i).
Proof. exact (MK_COMB (@lem6992462 A B t R i) (@lem6992461 A B i)). Qed.
Lemma lem6992464 {A B : Type'} (t : B -> Prop) (R : type1413 A B) : (term160 A B t R) = (term60 A B t R).
Proof. exact (fun_ext (fun i : A => @lem6992463 A B t R i)). Qed.
Lemma lem6992465 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@nsum A s).
Proof. exact (eq_refl (@nsum A s)). Qed.
Lemma lem6992466 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term149 A B s t R) = (term121 A B s t R).
Proof. exact (MK_COMB (@lem6992465 A s) (@lem6992464 A B t R)). Qed.
Lemma lem6992467 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6992468 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (R : type1413 A B) : (term161 A B s t R) = (term162 A B s t R).
Proof. exact (MK_COMB (@lem6992467) (@lem6992466 A B s t R)). Qed.
Lemma lem6992469 {A B : Type'} (i : A) : (term152 A B i) = (term153 B).
Proof. exact (eq_refl (term152 A B i)). Qed.
Lemma lem6992470 {B : Type'} (j : B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem6992471 {A B : Type'} (i : A) (j : B) : (term154 A B i j) = (term155 B j).
Proof. exact (MK_COMB (@lem6992469 A B i) (@lem6992470 B j)). Qed.
Lemma lem6992472 {B : Type'} (j : B) : (term155 B j) = term156.
Proof. exact (eq_refl (term155 B j)). Qed.
Lemma lem6992473 {A B : Type'} (i : A) (j : B) : (term154 A B i j) = term156.
Proof. exact (TRANS (@lem6992471 A B i j) (@lem6992472 B j)). Qed.
Lemma lem6992474 {A B : Type'} (j : B) : (term163 A B j) = (term153 A).
Proof. exact (fun_ext (fun i : A => @lem6992473 A B i j)). Qed.
Lemma lem6992475 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (j : B) : (term164 A B s R j) = (term164 A B s R j).
Proof. exact (eq_refl (term164 A B s R j)). Qed.
Lemma lem6992476 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (j : B) : (term165 A B s R j) = (term166 A B s R j).
Proof. exact (MK_COMB (@lem6992475 A B s R j) (@lem6992474 A B j)). Qed.
Lemma lem6992477 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : (term167 A B s R) = (term168 A B s R).
Proof. exact (fun_ext (fun j : B => @lem6992476 A B s R j)). Qed.
Lemma lem6992478 {B : Type'} (t : B -> Prop) : (@nsum B t) = (@nsum B t).
Proof. exact (eq_refl (@nsum B t)). Qed.
Lemma lem6992479 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) : (term150 A B t s R) = (term169 A B t s R).
Proof. exact (MK_COMB (@lem6992478 B t) (@lem6992477 A B s R)). Qed.
Lemma lem6992480 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) : ((term149 A B s t R) = (term150 A B t s R)) = ((term121 A B s t R) = (term169 A B t s R)).
Proof. exact (MK_COMB (@lem6992468 A B s t R) (@lem6992479 A B t s R)). Qed.
Lemma lem6992481 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (term121 A B s t R) = (term169 A B t s R).
Proof. exact (EQ_MP (@lem6992480 A B t s R) (@lem6992455 A B R s t h1)). Qed.
Lemma lem6992482 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6992483 {A B : Type'} (R : type1413 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (term162 A B s t R) = (term170 A B t s R).
Proof. exact (MK_COMB (@lem6992482) (@lem6992481 A B R s t h1)). Qed.
Lemma lem6992484 {B : Type'} (t : B -> Prop) (k : B -> nat) : (term52 B t k) = (term52 B t k).
Proof. exact (eq_refl (term52 B t k)). Qed.
Lemma lem6992485 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : ((term121 A B s t R) = (term52 B t k)) = ((term169 A B t s R) = (term52 B t k)).
Proof. exact (MK_COMB (@lem6992483 A B R s t h1) (@lem6992484 B t k)). Qed.
Lemma lem6992486 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : ((term169 A B t s R) = (term52 B t k)) = ((term121 A B s t R) = (term52 B t k)).
Proof. exact (SYM (@lem6992485 A B R k s t h1)). Qed.
Lemma lem6992488 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : term12 _127166 f s g.
Proof. exact (EQ_MP (@lem6992055 _127166 f s g) (@lem6992054 _127166 f s g)). Qed.
Lemma lem6992489 {B : Type'} (f : B -> nat) (s : B -> Prop) (g : B -> nat) : term12 B f s g.
Proof. exact (@lem6992488 B f s g). Qed.
Lemma lem6992490 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term171 A B s R t k.
Proof. exact (@lem6992489 B (term168 A B s R) t (term172 B k)). Qed.
Lemma lem6992491 {A : Type'} (s : A -> Prop) : term83 A s.
Proof. exact (@lem3603906 A s). Qed.
Lemma lem6992492 {A : Type'} (s : A -> Prop) : (term83 A s) = (term84 A s).
Proof. exact (eq_refl (term83 A s)). Qed.
Lemma lem6992493 {A : Type'} (s : A -> Prop) : term84 A s.
Proof. exact (EQ_MP (@lem6992492 A s) (@lem6992491 A s)). Qed.
Lemma lem6992494 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term85 A s P.
Proof. exact (@lem6992493 A s P). Qed.
Lemma lem6992495 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term85 A s P) = (term86 A s P).
Proof. exact (eq_refl (term85 A s P)). Qed.
Lemma lem6992496 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term86 A s P.
Proof. exact (EQ_MP (@lem6992495 A s P) (@lem6992494 A s P)). Qed.
Lemma lem6992497 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6992498 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term87 A s P.
Proof. exact (@lem6992496 A s P (@lem6992497 A s h1)). Qed.
Lemma lem6992499 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term87 A s P) = ((term87 A s P) = True).
Proof. exact (@lem7 (term87 A s P)). Qed.
Lemma lem6992500 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term87 A s P) = True.
Proof. exact (EQ_MP (@lem6992499 A s P) (@lem6992498 A P s h1)). Qed.
Lemma lem6992506 {_127196 : Type'} (c : nat) : term173 _127196 c.
Proof. exact (@lem6940531 _127196 c). Qed.
Lemma lem6992507 {_127196 : Type'} (c : nat) : (term173 _127196 c) = (term174 _127196 c).
Proof. exact (eq_refl (term173 _127196 c)). Qed.
Lemma lem6992508 {_127196 : Type'} (c : nat) : term174 _127196 c.
Proof. exact (EQ_MP (@lem6992507 _127196 c) (@lem6992506 _127196 c)). Qed.
Lemma lem6992509 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : term175 _127196 c s.
Proof. exact (@lem6992508 _127196 c s). Qed.
Lemma lem6992510 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term175 _127196 c s) = (term176 _127196 s c).
Proof. exact (eq_refl (term175 _127196 c s)). Qed.
Lemma lem6992511 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term176 _127196 s c.
Proof. exact (EQ_MP (@lem6992510 _127196 s c) (@lem6992509 _127196 c s)). Qed.
Lemma lem6992512 {_127196 : Type'} (s : _127196 -> Prop) (h1 : @FINITE _127196 s) : @FINITE _127196 s.
Proof. exact (h1). Qed.
Lemma lem6992513 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) (h1 : @FINITE _127196 s) : (term177 _127196 s c) = (term178 _127196 s c).
Proof. exact (@lem6992511 _127196 s c (@lem6992512 _127196 s h1)). Qed.
Lemma lem6992522 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : @FINITE A s.
Proof. exact (proj1 (@lem6992164 A B s t h1)). Qed.
Lemma lem6992523 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6992525 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term48 A B t s R k) : term179 A B t s R k j.
Proof. exact (@lem6992163 A B t s R k h1 j). Qed.
Lemma lem6992526 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (j : B) : (term179 A B t s R k j) = (term180 A B t s R k j).
Proof. exact (eq_refl (term179 A B t s R k j)). Qed.
Lemma lem6992527 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term48 A B t s R k) : term180 A B t s R k j.
Proof. exact (EQ_MP (@lem6992526 A B t s R k j) (@lem6992525 A B j t s R k h1)). Qed.
Lemma lem6992528 {B : Type'} (j : B) (t : B -> Prop) (h1 : @IN B j t) : @IN B j t.
Proof. exact (h1). Qed.
Lemma lem6992529 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (j : B) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : @IN B j t) : (term181 A B s R j) = (k j).
Proof. exact (@lem6992527 A B j t s R k h1 (@lem6992528 B j t h2)). Qed.
Lemma lem6992542 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term182 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6992543 (p : Prop) (q : Prop) (p' : Prop) : term183 p q p'.
Proof. exact (fun q' : Prop => @lem6992542 p q p' q'). Qed.
Lemma lem6992544 (p : Prop) (q : Prop) : term184 p q.
Proof. exact (fun p' : Prop => @lem6992543 p q p'). Qed.
Lemma lem6992545 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) : term185 A B t s R k x.
Proof. exact (@lem6992544 (@IN B x t) ((term186 A B s R x) = (term62 B k x))). Qed.
Lemma lem6992546 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (p' : Prop) : term187 A B t s R k x p'.
Proof. exact (@lem6992545 A B t s R k x p'). Qed.
Lemma lem6992547 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (p' : Prop) : (term187 A B t s R k x p') = (term188 A B t s R k x p').
Proof. exact (eq_refl (term187 A B t s R k x p')). Qed.
Lemma lem6992548 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (p' : Prop) : term188 A B t s R k x p'.
Proof. exact (EQ_MP (@lem6992547 A B t s R k x p') (@lem6992546 A B t s R k x p')). Qed.
Lemma lem6992549 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (p' : Prop) (q' : Prop) : term189 A B t s R k x p' q'.
Proof. exact (@lem6992548 A B t s R k x p' q'). Qed.
Lemma lem6992550 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (p' : Prop) (q' : Prop) : (term189 A B t s R k x p' q') = (term190 A B t s R k x p' q').
Proof. exact (eq_refl (term189 A B t s R k x p' q')). Qed.
Lemma lem6992551 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (p' : Prop) (q' : Prop) : term190 A B t s R k x p' q'.
Proof. exact (EQ_MP (@lem6992550 A B t s R k x p' q') (@lem6992549 A B t s R k x p' q')). Qed.
Lemma lem6992552 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (@IN B x t).
Proof. exact (eq_refl (@IN B x t)). Qed.
Lemma lem6992553 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (t : B -> Prop) (q' : Prop) : term191 A B s R k x t q'.
Proof. exact (@lem6992551 A B t s R k x (@IN B x t) q'). Qed.
Lemma lem6992554 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (t : B -> Prop) (q' : Prop) : term192 A B s R k x t q'.
Proof. exact (@lem6992553 A B s R k x t q' (@lem6992552 B x t)). Qed.
Lemma lem6992555 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : @IN B x t.
Proof. exact (h1). Qed.
Lemma lem6992556 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = ((@IN B x t) = True).
Proof. exact (@lem7 (@IN B x t)). Qed.
Lemma lem6992561 {A B : Type'} (f : A -> B) (y : A) : (term61 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6992562 {B : Type'} (f : B -> nat) (y : B) : (term62 B f y) = (f y).
Proof. exact (@lem6992561 B nat f y). Qed.
Lemma lem6992563 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term193 A B s R x) = (term186 A B s R x).
Proof. exact (@lem6992562 B (term168 A B s R) x). Qed.
Lemma lem6992564 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (j : B) : (term186 A B s R j) = (term166 A B s R j).
Proof. exact (eq_refl (term186 A B s R j)). Qed.
Lemma lem6992565 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : (term194 A B s R) = (term168 A B s R).
Proof. exact (fun_ext (fun j : B => @lem6992564 A B s R j)). Qed.
Lemma lem6992566 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6992567 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term193 A B s R x) = (term186 A B s R x).
Proof. exact (MK_COMB (@lem6992565 A B s R) (@lem6992566 B x)). Qed.
Lemma lem6992568 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6992569 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term195 A B s R x) = (term196 A B s R x).
Proof. exact (MK_COMB (@lem6992568) (@lem6992567 A B s R x)). Qed.
Lemma lem6992570 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term186 A B s R x) = (term166 A B s R x).
Proof. exact (eq_refl (term186 A B s R x)). Qed.
Lemma lem6992571 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : ((term193 A B s R x) = (term186 A B s R x)) = ((term186 A B s R x) = (term166 A B s R x)).
Proof. exact (MK_COMB (@lem6992569 A B s R x) (@lem6992570 A B s R x)). Qed.
Lemma lem6992572 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term186 A B s R x) = (term166 A B s R x).
Proof. exact (EQ_MP (@lem6992571 A B s R x) (@lem6992563 A B s R x)). Qed.
Lemma lem6992574 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term176 _127196 s c.
Proof. exact (fun h0 : @FINITE _127196 s => @lem6992513 _127196 c s h0). Qed.
Lemma lem6992575 {A : Type'} (s : A -> Prop) (c : nat) : term176 A s c.
Proof. exact (@lem6992574 A s c). Qed.
Lemma lem6992576 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : term197 A B s R x.
Proof. exact (@lem6992575 A (term198 A B s R x) term156). Qed.
Lemma lem6992578 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term93 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem6992500 A P s h0). Qed.
Lemma lem6992579 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term93 A s P.
Proof. exact (@lem6992578 A s P). Qed.
Lemma lem6992580 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : term199 A B s R x.
Proof. exact (@lem6992579 A s (term200 A B R x)). Qed.
Lemma lem6992581 {A B : Type'} (R : type1413 A B) (i : A) (x : B) : (term201 A B R x i) = (R i x).
Proof. exact (eq_refl (term201 A B R x i)). Qed.
Lemma lem6992582 {A : Type'} (i : A) (s : A -> Prop) : (term97 A i s) = (term97 A i s).
Proof. exact (eq_refl (term97 A i s)). Qed.
Lemma lem6992583 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (i : A) (x : B) : (term202 A B s R x i) = (term203 A B s R i x).
Proof. exact (MK_COMB (@lem6992582 A i s) (@lem6992581 A B R i x)). Qed.
Lemma lem6992584 {A : Type'} (GEN_PVAR_289 : A) : (@SETSPEC A GEN_PVAR_289) = (@SETSPEC A GEN_PVAR_289).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_289)). Qed.
Lemma lem6992585 {A B : Type'} (GEN_PVAR_289 : A) (s : A -> Prop) (R : type1413 A B) (i : A) (x : B) : (term204 A B GEN_PVAR_289 s R x i) = (term205 A B GEN_PVAR_289 s R i x).
Proof. exact (MK_COMB (@lem6992584 A GEN_PVAR_289) (@lem6992583 A B s R i x)). Qed.
Lemma lem6992586 {A : Type'} (i : A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6992587 {A B : Type'} (GEN_PVAR_289 : A) (s : A -> Prop) (R : type1413 A B) (x : B) (i : A) : (term206 A B GEN_PVAR_289 s R x i) = (term207 A B GEN_PVAR_289 s R x i).
Proof. exact (MK_COMB (@lem6992585 A B GEN_PVAR_289 s R i x) (@lem6992586 A i)). Qed.
Lemma lem6992588 {A B : Type'} (GEN_PVAR_289 : A) (s : A -> Prop) (R : type1413 A B) (x : B) : (term208 A B GEN_PVAR_289 s R x) = (term209 A B GEN_PVAR_289 s R x).
Proof. exact (fun_ext (fun i : A => @lem6992587 A B GEN_PVAR_289 s R x i)). Qed.
Lemma lem6992589 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6992590 {A B : Type'} (GEN_PVAR_289 : A) (s : A -> Prop) (R : type1413 A B) (x : B) : (term210 A B GEN_PVAR_289 s R x) = (term211 A B GEN_PVAR_289 s R x).
Proof. exact (MK_COMB (@lem6992589 A) (@lem6992588 A B GEN_PVAR_289 s R x)). Qed.
Lemma lem6992591 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term212 A B s R x) = (term213 A B s R x).
Proof. exact (fun_ext (fun GEN_PVAR_289 : A => @lem6992590 A B GEN_PVAR_289 s R x)). Qed.
Lemma lem6992592 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem6992593 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term214 A B s R x) = (term198 A B s R x).
Proof. exact (MK_COMB (@lem6992592 A) (@lem6992591 A B s R x)). Qed.
Lemma lem6992594 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem6992595 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term215 A B s R x) = (term216 A B s R x).
Proof. exact (MK_COMB (@lem6992594 A) (@lem6992593 A B s R x)). Qed.
Lemma lem6992596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6992597 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term217 A B s R x) = (term218 A B s R x).
Proof. exact (MK_COMB (@lem6992596) (@lem6992595 A B s R x)). Qed.
Lemma lem6992598 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem6992599 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : ((term215 A B s R x) = True) = ((term216 A B s R x) = True).
Proof. exact (MK_COMB (@lem6992597 A B s R x) (@lem6992598)). Qed.
Lemma lem6992600 {A : Type'} (s : A -> Prop) : (term115 A s) = (term115 A s).
Proof. exact (eq_refl (term115 A s)). Qed.
Lemma lem6992601 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : (term199 A B s R x) = (term219 A B s R x).
Proof. exact (MK_COMB (@lem6992600 A s) (@lem6992599 A B s R x)). Qed.
Lemma lem6992602 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (x : B) : term219 A B s R x.
Proof. exact (EQ_MP (@lem6992601 A B s R x) (@lem6992580 A B s R x)). Qed.
Lemma lem6992604 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6992523 A s) (@lem6992522 A B s t h1)). Qed.
Lemma lem6992605 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : True = (@FINITE A s).
Proof. exact (SYM (@lem6992604 A B s t h1)). Qed.
Lemma lem6992606 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : @FINITE A s.
Proof. exact (EQ_MP (@lem6992605 A B s t h1) (@lem0)). Qed.
Lemma lem6992607 {A B : Type'} (R : type1413 A B) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (term216 A B s R x) = True.
Proof. exact (@lem6992602 A B s R x (@lem6992606 A B s t h1)). Qed.
Lemma lem6992608 {A B : Type'} (R : type1413 A B) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : True = (term216 A B s R x).
Proof. exact (SYM (@lem6992607 A B R x s t h1)). Qed.
Lemma lem6992609 {A B : Type'} (R : type1413 A B) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : term216 A B s R x.
Proof. exact (EQ_MP (@lem6992608 A B R x s t h1) (@lem0)). Qed.
Lemma lem6992610 {A B : Type'} (R : type1413 A B) (x : B) (s : A -> Prop) (t : B -> Prop) (h1 : term55 A B s t) : (term166 A B s R x) = (term220 A B s R x).
Proof. exact (@lem6992576 A B s R x (@lem6992609 A B R x s t h1)). Qed.
Lemma lem6992612 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term48 A B t s R k) : term180 A B t s R k j.
Proof. exact (fun h0 : @IN B j t => @lem6992529 A B s R k j t h1 h0). Qed.
Lemma lem6992613 {A B : Type'} (j : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term48 A B t s R k) : term180 A B t s R k j.
Proof. exact (@lem6992612 A B j t s R k h1). Qed.
Lemma lem6992614 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term48 A B t s R k) : term180 A B t s R k x.
Proof. exact (@lem6992613 A B x t s R k h1). Qed.
Lemma lem6992616 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : (@IN B x t) = True.
Proof. exact (EQ_MP (@lem6992556 B x t) (@lem6992555 B x t h1)). Qed.
Lemma lem6992617 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : True = (@IN B x t).
Proof. exact (SYM (@lem6992616 B x t h1)). Qed.
Lemma lem6992618 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : @IN B x t.
Proof. exact (EQ_MP (@lem6992617 B x t h1) (@lem0)). Qed.
Lemma lem6992619 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : @IN B x t) : (term181 A B s R x) = (k x).
Proof. exact (@lem6992614 A B x t s R k h1 (@lem6992618 B x t h2)). Qed.
Lemma lem6992620 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem6992621 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : @IN B x t) : (term221 A B s R x) = (term222 B k x).
Proof. exact (MK_COMB (@lem6992620) (@lem6992619 A B s R k x t h1 h2)). Qed.
Lemma lem6992622 : term156 = term156.
Proof. exact (eq_refl term156). Qed.
Lemma lem6992623 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (x : B) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : @IN B x t) : (term220 A B s R x) = (term223 B k x).
Proof. exact (MK_COMB (@lem6992621 A B s R k x t h1 h2) (@lem6992622)). Qed.
Lemma lem6992624 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) (h3 : @IN B x t) : (term166 A B s R x) = (term223 B k x).
Proof. exact (TRANS (@lem6992610 A B R x s t h2) (@lem6992623 A B s R k x t h1 h3)). Qed.
Lemma lem6992625 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) (h3 : @IN B x t) : (term186 A B s R x) = (term223 B k x).
Proof. exact (TRANS (@lem6992572 A B s R x) (@lem6992624 A B R k s x t h1 h2 h3)). Qed.
Lemma lem6992626 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6992627 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) (h3 : @IN B x t) : (term196 A B s R x) = (term224 B k x).
Proof. exact (MK_COMB (@lem6992626) (@lem6992625 A B R k s x t h1 h2 h3)). Qed.
Lemma lem6992629 {A B : Type'} (f : A -> B) (y : A) : (term61 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6992630 {B : Type'} (f : B -> nat) (y : B) : (term62 B f y) = (f y).
Proof. exact (@lem6992629 B nat f y). Qed.
Lemma lem6992631 {B : Type'} (k : B -> nat) (x : B) : (term62 B k x) = (k x).
Proof. exact (@lem6992630 B k x). Qed.
Lemma lem6992632 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (x : B) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) (h3 : @IN B x t) : ((term186 A B s R x) = (term62 B k x)) = ((term223 B k x) = (k x)).
Proof. exact (MK_COMB (@lem6992627 A B R k s x t h1 h2 h3) (@lem6992631 B k x)). Qed.
Lemma lem6992635 {A B : Type'} (x : B) (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : term225 A B t s R k x.
Proof. exact (fun h0 : @IN B x t => @lem6992632 A B R k s x t h1 h2 h0). Qed.
Lemma lem6992636 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) (x : B) : term226 A B s R t k x.
Proof. exact (@lem6992554 A B s R k x t ((term223 B k x) = (k x))). Qed.
Lemma lem6992637 {A B : Type'} (x : B) (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : (term227 A B t s R k x) = (term228 B t k x).
Proof. exact (@lem6992636 A B s R t k x (@lem6992635 A B x R k s t h1 h2)). Qed.
Lemma lem6992665 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : (term229 A B t s R k) = (term230 B t k).
Proof. exact (fun_ext (fun x : B => @lem6992637 A B x R k s t h1 h2)). Qed.
Lemma lem6992693 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6992694 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : (term231 A B t s R k) = (term232 B t k).
Proof. exact (MK_COMB (@lem6992693 B) (@lem6992665 A B R k s t h1 h2)). Qed.
Lemma lem6992726 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : (term232 B t k) = (term231 A B t s R k).
Proof. exact (SYM (@lem6992694 A B R k s t h1 h2)). Qed.
Lemma lem6992736 (m : nat) : (term5 m) = m.
Proof. exact (EQ_MP (@lem6992013 m) (@lem6992012 m)). Qed.
Lemma lem6992737 {B : Type'} (k : B -> nat) (x : B) : (term223 B k x) = (k x).
Proof. exact (@lem6992736 (k x)). Qed.
Lemma lem6992738 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6992739 {B : Type'} (k : B -> nat) (x : B) : (term224 B k x) = (term233 B k x).
Proof. exact (MK_COMB (@lem6992738) (@lem6992737 B k x)). Qed.
Lemma lem6992740 {B : Type'} (k : B -> nat) (x : B) : (k x) = (k x).
Proof. exact (eq_refl (k x)). Qed.
Lemma lem6992741 {B : Type'} (k : B -> nat) (x : B) : ((term223 B k x) = (k x)) = ((k x) = (k x)).
Proof. exact (MK_COMB (@lem6992739 B k x) (@lem6992740 B k x)). Qed.
Lemma lem6992743 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6992744 (x : nat) : (x = x) = True.
Proof. exact (@lem6992743 nat x). Qed.
Lemma lem6992745 {B : Type'} (k : B -> nat) (x : B) : ((k x) = (k x)) = True.
Proof. exact (@lem6992744 (k x)). Qed.
Lemma lem6992746 {B : Type'} (k : B -> nat) (x : B) : ((term223 B k x) = (k x)) = True.
Proof. exact (TRANS (@lem6992741 B k x) (@lem6992745 B k x)). Qed.
Lemma lem6992747 {B : Type'} (x : B) (t : B -> Prop) : (term76 B x t) = (term76 B x t).
Proof. exact (eq_refl (term76 B x t)). Qed.
Lemma lem6992748 {B : Type'} (k : B -> nat) (x : B) (t : B -> Prop) : (term228 B t k x) = (term234 B x t).
Proof. exact (MK_COMB (@lem6992747 B x t) (@lem6992746 B k x)). Qed.
Lemma lem6992750 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6992751 {B : Type'} (x : B) (t : B -> Prop) : (term234 B x t) = True.
Proof. exact (@lem6992750 (@IN B x t)). Qed.
Lemma lem6992752 {B : Type'} (t : B -> Prop) (k : B -> nat) (x : B) : (term228 B t k x) = True.
Proof. exact (TRANS (@lem6992748 B k x t) (@lem6992751 B x t)). Qed.
Lemma lem6992753 {B : Type'} (t : B -> Prop) (k : B -> nat) : (term230 B t k) = (term235 B).
Proof. exact (fun_ext (fun x : B => @lem6992752 B t k x)). Qed.
Lemma lem6992754 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6992755 {B : Type'} (t : B -> Prop) (k : B -> nat) : (term232 B t k) = (term236 B).
Proof. exact (MK_COMB (@lem6992754 B) (@lem6992753 B t k)). Qed.
Lemma lem6992757 {A : Type'} (t : Prop) : (term237 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6992758 {B : Type'} (t : Prop) : (term237 B t) = t.
Proof. exact (@lem6992757 B t). Qed.
Lemma lem6992759 {B : Type'} : (term236 B) = True.
Proof. exact (@lem6992758 B True). Qed.
Lemma lem6992760 {B : Type'} (t : B -> Prop) (k : B -> nat) : (term232 B t k) = True.
Proof. exact (TRANS (@lem6992755 B t k) (@lem6992759 B)). Qed.
Lemma lem6992761 {B : Type'} (t : B -> Prop) (k : B -> nat) : True = (term232 B t k).
Proof. exact (SYM (@lem6992760 B t k)). Qed.
Lemma lem6992762 {B : Type'} (t : B -> Prop) (k : B -> nat) : term232 B t k.
Proof. exact (EQ_MP (@lem6992761 B t k) (@lem0)). Qed.
Lemma lem6992763 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : term231 A B t s R k.
Proof. exact (EQ_MP (@lem6992726 A B R k s t h1 h2) (@lem6992762 B t k)). Qed.
Lemma lem6992764 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : (term169 A B t s R) = (term52 B t k).
Proof. exact (@lem6992490 A B s R t k (@lem6992763 A B R k s t h1 h2)). Qed.
Lemma lem6992765 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : (term121 A B s t R) = (term52 B t k).
Proof. exact (EQ_MP (@lem6992486 A B R k s t h2) (@lem6992764 A B R k s t h1 h2)). Qed.
Lemma lem6992766 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : term238 A B s R t k.
Proof. exact (conj (@lem6992381 A B R s t h2) (@lem6992765 A B R k s t h1 h2)). Qed.
Lemma lem6992767 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : term239 A B s R t k.
Proof. exact (ex_intro (term240 A B s R t k) (term121 A B s t R) (@lem6992766 A B R k s t h1 h2)). Qed.
Lemma lem6992768 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : (term51 A B s t R) = (term52 B t k).
Proof. exact (@lem6992168 A B s R t k (@lem6992767 A B R k s t h1 h2)). Qed.
Lemma lem6992769 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term47 A B t s R k) : term48 A B t s R k.
Proof. exact (proj2 (@lem6992162 A B t s R k h1)). Qed.
Lemma lem6992770 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term47 A B t s R k) : term55 A B s t.
Proof. exact (proj1 (@lem6992162 A B t s R k h1)). Qed.
Lemma lem6992771 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : (term48 A B t s R k) = ((term51 A B s t R) = (term52 B t k)).
Proof. exact (prop_ext (fun h3 : term48 A B t s R k => @lem6992768 A B R k s t h1 h2) (fun h3 : (term51 A B s t R) = (term52 B t k) => @lem6992163 A B t s R k h1)). Qed.
Lemma lem6992772 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : (term51 A B s t R) = (term52 B t k).
Proof. exact (EQ_MP (@lem6992771 A B R k s t h1 h2) (@lem6992163 A B t s R k h1)). Qed.
Lemma lem6992773 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : (term55 A B s t) = ((term51 A B s t R) = (term52 B t k)).
Proof. exact (prop_ext (fun h3 : term55 A B s t => @lem6992772 A B R k s t h1 h2) (fun h3 : (term51 A B s t R) = (term52 B t k) => @lem6992164 A B s t h2)). Qed.
Lemma lem6992774 {A B : Type'} (R : type1413 A B) (k : B -> nat) (s : A -> Prop) (t : B -> Prop) (h1 : term48 A B t s R k) (h2 : term55 A B s t) : (term51 A B s t R) = (term52 B t k).
Proof. exact (EQ_MP (@lem6992773 A B R k s t h1 h2) (@lem6992164 A B s t h2)). Qed.
Lemma lem6992775 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term55 A B s t) (h2 : term47 A B t s R k) : (term48 A B t s R k) = ((term51 A B s t R) = (term52 B t k)).
Proof. exact (prop_ext (fun h3 : term48 A B t s R k => @lem6992774 A B R k s t h3 h1) (fun h3 : (term51 A B s t R) = (term52 B t k) => @lem6992769 A B t s R k h2)). Qed.
Lemma lem6992776 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term55 A B s t) (h2 : term47 A B t s R k) : (term51 A B s t R) = (term52 B t k).
Proof. exact (EQ_MP (@lem6992775 A B t s R k h1 h2) (@lem6992769 A B t s R k h2)). Qed.
Lemma lem6992777 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term47 A B t s R k) : (term55 A B s t) = ((term51 A B s t R) = (term52 B t k)).
Proof. exact (prop_ext (fun h2 : term55 A B s t => @lem6992776 A B t s R k h2 h1) (fun h2 : (term51 A B s t R) = (term52 B t k) => @lem6992770 A B t s R k h1)). Qed.
Lemma lem6992778 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (R : type1413 A B) (k : B -> nat) (h1 : term47 A B t s R k) : (term51 A B s t R) = (term52 B t k).
Proof. exact (EQ_MP (@lem6992777 A B t s R k h1) (@lem6992770 A B t s R k h1)). Qed.
Lemma lem6992779 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term54 A B s R t k.
Proof. exact (fun h0 : term47 A B t s R k => @lem6992778 A B t s R k h0). Qed.
Lemma lem6992780 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) (k : B -> nat) : term53 A B s R t k.
Proof. exact (EQ_MP (@lem6992161 A B s R t k) (@lem6992779 A B s R t k)). Qed.
Lemma lem6992785 {A B : Type'} (s : A -> Prop) (R : type1413 A B) (t : B -> Prop) : term241 A B s R t.
Proof. exact (fun k : B -> nat => @lem6992780 A B s R t k). Qed.
Lemma lem6992790 {A B : Type'} (s : A -> Prop) (R : type1413 A B) : term242 A B s R.
Proof. exact (fun t : B -> Prop => @lem6992785 A B s R t). Qed.
Lemma lem6992795 {A B : Type'} (R : type1413 A B) : term243 A B R.
Proof. exact (fun s : A -> Prop => @lem6992790 A B s R). Qed.
Lemma lem6992800 {A B : Type'} : term244 A B.
Proof. exact (fun R : type1413 A B => @lem6992795 A B R). Qed.

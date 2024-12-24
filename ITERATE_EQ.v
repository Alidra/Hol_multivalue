Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IN_INSERT_spec.
Require Import IN_SUPPORT_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import ITERATE_EXPAND_CASES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1821_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm196_spec.
Require Import thm197_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem5970053 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem5970054 {A : Type'} (P : type686 A) (h1 : term0 A) : term1 A P.
Proof. exact (@lem5970053 A h1 P). Qed.
Lemma lem5970055 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem5970056 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem5970055 A P) (@lem5970054 A P h1)). Qed.
Lemma lem5970057 {A : Type'} (P : type686 A) (h1 : term3 A P) : term3 A P.
Proof. exact (h1). Qed.
Lemma lem5970058 {A : Type'} (P : type686 A) (h1 : term0 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem5970056 A P h1 (@lem5970057 A P h2)). Qed.
Lemma lem5970059 {A : Type'} (P : type686 A) (h1 : term3 A P) : term5 A P.
Proof. exact (fun h0 : term0 A => @lem5970058 A P h0 h1). Qed.
Lemma lem5970060 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem5970061 {A : Type'} (P : type686 A) (h1 : term0 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem5970059 A P h2 (@lem5970060 A h1)). Qed.
Lemma lem5970062 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (fun h0 : term3 A P => @lem5970061 A P h1 h0). Qed.
Lemma lem5970063 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : type686 A => @lem5970062 A P h1). Qed.
Lemma lem5970064 {A : Type'} : term6 A.
Proof. exact (fun h0 : term0 A => @lem5970063 A h0). Qed.
Lemma lem5970065 {A : Type'} : term0 A.
Proof. exact (@lem5970064 A (@lem3558722 A)). Qed.
Lemma lem5970066 {A : Type'} (P : type686 A) : term1 A P.
Proof. exact (@lem5970065 A P). Qed.
Lemma lem5970067 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem5970089 {_119826 _119829 : Type'} (op : type1400 _119826) : term7 _119826 _119829 op.
Proof. exact (@lem5718201 _119826 _119829 op). Qed.
Lemma lem5970090 {_119826 _119829 : Type'} (op : type1400 _119826) : (term7 _119826 _119829 op) = (term8 _119826 _119829 op).
Proof. exact (eq_refl (term7 _119826 _119829 op)). Qed.
Lemma lem5970091 {_119826 _119829 : Type'} (op : type1400 _119826) : term8 _119826 _119829 op.
Proof. exact (EQ_MP (@lem5970090 _119826 _119829 op) (@lem5970089 _119826 _119829 op)). Qed.
Lemma lem5970092 {_119826 _119829 : Type'} (op : type1400 _119826) (f : _119829 -> _119826) : term9 _119826 _119829 op f.
Proof. exact (@lem5970091 _119826 _119829 op f). Qed.
Lemma lem5970093 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) : (term9 _119826 _119829 op f) = (term10 _119826 _119829 f op).
Proof. exact (eq_refl (term9 _119826 _119829 op f)). Qed.
Lemma lem5970094 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) : term10 _119826 _119829 f op.
Proof. exact (EQ_MP (@lem5970093 _119826 _119829 f op) (@lem5970092 _119826 _119829 op f)). Qed.
Lemma lem5970095 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) (x : _119829) : term11 _119826 _119829 f op x.
Proof. exact (@lem5970094 _119826 _119829 f op x). Qed.
Lemma lem5970096 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term11 _119826 _119829 f op x) = (term12 _119826 _119829 f x op).
Proof. exact (eq_refl (term11 _119826 _119829 f op x)). Qed.
Lemma lem5970097 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : term12 _119826 _119829 f x op.
Proof. exact (EQ_MP (@lem5970096 _119826 _119829 f x op) (@lem5970095 _119826 _119829 f op x)). Qed.
Lemma lem5970098 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) (s : _119829 -> Prop) : term13 _119826 _119829 f x op s.
Proof. exact (@lem5970097 _119826 _119829 f x op s). Qed.
Lemma lem5970099 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term13 _119826 _119829 f x op s) = ((term14 _119826 _119829 x op f s) = (term15 _119826 _119829 s f x op)).
Proof. exact (eq_refl (term13 _119826 _119829 f x op s)). Qed.
Lemma lem5970101 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5970102 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem5970103 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem5970102 A s) (@lem5970101 A s)). Qed.
Lemma lem5970104 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem5970103 A s t). Qed.
Lemma lem5970105 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = ((s = t) = (term19 A s t)).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem5970107 {_120327 _120333 : Type'} (op : type1400 _120327) : term20 _120327 _120333 op.
Proof. exact (@lem5738118 _120327 _120333 op). Qed.
Lemma lem5970108 {_120327 _120333 : Type'} (op : type1400 _120327) : (term20 _120327 _120333 op) = (term21 _120327 _120333 op).
Proof. exact (eq_refl (term20 _120327 _120333 op)). Qed.
Lemma lem5970109 {_120327 _120333 : Type'} (op : type1400 _120327) : term21 _120327 _120333 op.
Proof. exact (EQ_MP (@lem5970108 _120327 _120333 op) (@lem5970107 _120327 _120333 op)). Qed.
Lemma lem5970110 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) : term22 _120327 _120333 op f.
Proof. exact (@lem5970109 _120327 _120333 op f). Qed.
Lemma lem5970111 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : (term22 _120327 _120333 op f) = (term23 _120327 _120333 f op).
Proof. exact (eq_refl (term22 _120327 _120333 op f)). Qed.
Lemma lem5970112 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : term23 _120327 _120333 f op.
Proof. exact (EQ_MP (@lem5970111 _120327 _120333 f op) (@lem5970110 _120327 _120333 op f)). Qed.
Lemma lem5970113 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) (s : _120333 -> Prop) : term24 _120327 _120333 f op s.
Proof. exact (@lem5970112 _120327 _120333 f op s). Qed.
Lemma lem5970114 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (term24 _120327 _120333 f op s) = ((@iterate _120327 _120333 op s f) = (term25 _120327 _120333 s f op)).
Proof. exact (eq_refl (term24 _120327 _120333 f op s)). Qed.
Lemma lem5970116 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5970117 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term26 A B s f g.
Proof. exact (h1). Qed.
Lemma lem5970121 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (@iterate _120327 _120333 op s f) = (term25 _120327 _120333 s f op).
Proof. exact (EQ_MP (@lem5970114 _120327 _120333 s f op) (@lem5970113 _120327 _120333 f op s)). Qed.
Lemma lem5970122 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@iterate B A op s f) = (term27 A B s f op).
Proof. exact (@lem5970121 B A s f op). Qed.
Lemma lem5970123 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5970124 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term28 A B op s f) = (term29 A B s f op).
Proof. exact (MK_COMB (@lem5970123 B) (@lem5970122 A B s f op)). Qed.
Lemma lem5970126 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (@iterate _120327 _120333 op s f) = (term25 _120327 _120333 s f op).
Proof. exact (EQ_MP (@lem5970114 _120327 _120333 s f op) (@lem5970113 _120327 _120333 f op s)). Qed.
Lemma lem5970127 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@iterate B A op s f) = (term27 A B s f op).
Proof. exact (@lem5970126 B A s f op). Qed.
Lemma lem5970128 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) : (@iterate B A op s g) = (term27 A B s g op).
Proof. exact (@lem5970127 A B s g op). Qed.
Lemma lem5970129 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((@iterate B A op s f) = (@iterate B A op s g)) = ((term27 A B s f op) = (term27 A B s g op)).
Proof. exact (MK_COMB (@lem5970124 A B s f op) (@lem5970128 A B s g op)). Qed.
Lemma lem5970130 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (g : A -> B) : ((term27 A B s f op) = (term27 A B s g op)) = ((@iterate B A op s f) = (@iterate B A op s g)).
Proof. exact (SYM (@lem5970129 A B f s g op)). Qed.
Lemma lem5970131 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (@support A B op g s) = (@support A B op f s)) : (@support A B op g s) = (@support A B op f s).
Proof. exact (h1). Qed.
Lemma lem5970132 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : (term30 A B s f g op) = (term30 A B s f g op).
Proof. exact (eq_refl (term30 A B s f g op)). Qed.
Lemma lem5970133 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (@support A B op g s) = (@support A B op f s)) : (term31 A B f op g s) = (term32 A B g op f s).
Proof. exact (MK_COMB (@lem5970132 A B s f g op) (@lem5970131 A B g op f s h1)). Qed.
Lemma lem5970134 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term32 A B g op f s) = ((term27 A B s f op) = (term33 A B f s g op)).
Proof. exact (eq_refl (term32 A B g op f s)). Qed.
Lemma lem5970135 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (s : A -> Prop) : (term34 A B f op g s) = (term34 A B f op g s).
Proof. exact (eq_refl (term34 A B f op g s)). Qed.
Lemma lem5970136 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term31 A B f op g s) = (term32 A B g op f s)) = ((term31 A B f op g s) = ((term27 A B s f op) = (term33 A B f s g op))).
Proof. exact (MK_COMB (@lem5970135 A B f op g s) (@lem5970134 A B f s g op)). Qed.
Lemma lem5970137 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term31 A B f op g s) = ((term27 A B s f op) = (term27 A B s g op)).
Proof. exact (eq_refl (term31 A B f op g s)). Qed.
Lemma lem5970138 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5970139 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term34 A B f op g s) = (term35 A B f s g op).
Proof. exact (MK_COMB (@lem5970138) (@lem5970137 A B f s g op)). Qed.
Lemma lem5970140 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term27 A B s f op) = (term33 A B f s g op)) = ((term27 A B s f op) = (term33 A B f s g op)).
Proof. exact (eq_refl ((term27 A B s f op) = (term33 A B f s g op))). Qed.
Lemma lem5970141 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term31 A B f op g s) = ((term27 A B s f op) = (term33 A B f s g op))) = (((term27 A B s f op) = (term27 A B s g op)) = ((term27 A B s f op) = (term33 A B f s g op))).
Proof. exact (MK_COMB (@lem5970139 A B f s g op) (@lem5970140 A B f s g op)). Qed.
Lemma lem5970142 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term31 A B f op g s) = (term32 A B g op f s)) = (((term27 A B s f op) = (term27 A B s g op)) = ((term27 A B s f op) = (term33 A B f s g op))).
Proof. exact (TRANS (@lem5970136 A B f s g op) (@lem5970141 A B f s g op)). Qed.
Lemma lem5970143 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (@support A B op g s) = (@support A B op f s)) : ((term27 A B s f op) = (term27 A B s g op)) = ((term27 A B s f op) = (term33 A B f s g op)).
Proof. exact (EQ_MP (@lem5970142 A B f s g op) (@lem5970133 A B g op f s h1)). Qed.
Lemma lem5970144 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (@support A B op g s) = (@support A B op f s)) : ((term27 A B s f op) = (term33 A B f s g op)) = ((term27 A B s f op) = (term27 A B s g op)).
Proof. exact (SYM (@lem5970143 A B g op f s h1)). Qed.
Lemma lem5970148 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem5970105 A s t) (@lem5970104 A s t)). Qed.
Lemma lem5970149 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (@lem5970148 A s t). Qed.
Lemma lem5970150 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) : ((@support A B op g s) = (@support A B op f s)) = (term36 A B g op f s).
Proof. exact (@lem5970149 A (@support A B op g s) (@support A B op f s)). Qed.
Lemma lem5970160 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term14 _119826 _119829 x op f s) = (term15 _119826 _119829 s f x op).
Proof. exact (EQ_MP (@lem5970099 _119826 _119829 s f x op) (@lem5970098 _119826 _119829 f x op s)). Qed.
Lemma lem5970161 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term37 A B x op f s) = (term38 A B s f x op).
Proof. exact (@lem5970160 B A s f x op). Qed.
Lemma lem5970162 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term37 A B x op g s) = (term38 A B s g x op).
Proof. exact (@lem5970161 A B s g x op). Qed.
Lemma lem5970169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5970170 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term39 A B x op g s) = (term40 A B s g x op).
Proof. exact (MK_COMB (@lem5970169) (@lem5970162 A B s g x op)). Qed.
Lemma lem5970172 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term14 _119826 _119829 x op f s) = (term15 _119826 _119829 s f x op).
Proof. exact (EQ_MP (@lem5970099 _119826 _119829 s f x op) (@lem5970098 _119826 _119829 f x op s)). Qed.
Lemma lem5970173 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term37 A B x op f s) = (term38 A B s f x op).
Proof. exact (@lem5970172 B A s f x op). Qed.
Lemma lem5970180 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term37 A B x op g s) = (term37 A B x op f s)) = ((term38 A B s g x op) = (term38 A B s f x op)).
Proof. exact (MK_COMB (@lem5970170 A B s g x op) (@lem5970173 A B s f x op)). Qed.
Lemma lem5970185 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term41 A B g op f s) = (term42 A B g s f op).
Proof. exact (fun_ext (fun x : A => @lem5970180 A B g s f x op)). Qed.
Lemma lem5970186 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5970187 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term36 A B g op f s) = (term43 A B g s f op).
Proof. exact (MK_COMB (@lem5970186 A) (@lem5970185 A B g s f op)). Qed.
Lemma lem5970192 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : ((@support A B op g s) = (@support A B op f s)) = (term43 A B g s f op).
Proof. exact (TRANS (@lem5970150 A B g op f s) (@lem5970187 A B g s f op)). Qed.
Lemma lem5970193 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term43 A B g s f op) = ((@support A B op g s) = (@support A B op f s)).
Proof. exact (SYM (@lem5970192 A B g s f op)). Qed.
Lemma lem5970195 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5970196 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term43 A B g s f op) = (term45 A B g s f op).
Proof. exact (@lem5970195 (term43 A B g s f op)). Qed.
Lemma lem5970197 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term45 A B g s f op) = (term43 A B g s f op).
Proof. exact (SYM (@lem5970196 A B g s f op)). Qed.
Lemma lem5970198 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term46 A B g s f op) : term46 A B g s f op.
Proof. exact (h1). Qed.
Lemma lem5970201 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term47 A B g s f op) : term47 A B g s f op.
Proof. exact (h1). Qed.
Lemma lem5970202 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term48 A B g s f op.
Proof. exact (fun h0 : term47 A B g s f op => @lem5970201 A B g s f op h0). Qed.
Lemma lem5970203 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term48 A B g s f op) : term48 A B g s f op.
Proof. exact (h1). Qed.
Lemma lem5970204 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term47 A B g s f op) : term47 A B g s f op.
Proof. exact (h1). Qed.
Lemma lem5970205 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term47 A B g s f op) (h2 : term48 A B g s f op) : term47 A B g s f op.
Proof. exact (@lem5970203 A B g s f op h2 (@lem5970204 A B g s f op h1)). Qed.
Lemma lem5970206 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term47 A B g s f op) : term49 A B g s f op.
Proof. exact (fun h0 : term48 A B g s f op => @lem5970205 A B g s f op h1 h0). Qed.
Lemma lem5970207 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term48 A B g s f op) : term48 A B g s f op.
Proof. exact (h1). Qed.
Lemma lem5970208 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term47 A B g s f op) (h2 : term48 A B g s f op) : term47 A B g s f op.
Proof. exact (@lem5970206 A B g s f op h1 (@lem5970207 A B g s f op h2)). Qed.
Lemma lem5970209 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term48 A B g s f op) : term48 A B g s f op.
Proof. exact (fun h0 : term47 A B g s f op => @lem5970208 A B g s f op h0 h1). Qed.
Lemma lem5970210 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term50 A B g s f op.
Proof. exact (fun h0 : term48 A B g s f op => @lem5970209 A B g s f op h0). Qed.
Lemma lem5970213 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term48 A B g s f op.
Proof. exact (@lem5970210 A B g s f op (@lem5970202 A B g s f op)). Qed.
Lemma lem5970214 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term48 A B g s f op.
Proof. exact (@lem5970213 A B g s f op). Qed.
Lemma lem5970242 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5970243 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term45 A B g s f op) = (term51 A B g s f op).
Proof. exact (@lem5970242 (term46 A B g s f op)). Qed.
Lemma lem5970245 (t : Prop) : (term52 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5970246 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term51 A B g s f op) = (term43 A B g s f op).
Proof. exact (@lem5970245 (term43 A B g s f op)). Qed.
Lemma lem5970251 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term45 A B g s f op) = (term43 A B g s f op).
Proof. exact (TRANS (@lem5970243 A B g s f op) (@lem5970246 A B g s f op)). Qed.
Lemma lem5970256 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term53 A B s f g) = (term53 A B s f g).
Proof. exact (eq_refl (term53 A B s f g)). Qed.
Lemma lem5970257 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term54 A B g s f op) = (term55 A B g s f op).
Proof. exact (MK_COMB (@lem5970256 A B s f g) (@lem5970251 A B g s f op)). Qed.
Lemma lem5970260 {B : Type'} (op : type1400 B) : (term56 B op) = (term56 B op).
Proof. exact (eq_refl (term56 B op)). Qed.
Lemma lem5970261 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term47 A B g s f op) = (term57 A B g s f op).
Proof. exact (MK_COMB (@lem5970260 B op) (@lem5970257 A B g s f op)). Qed.
Lemma lem5970264 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term58 A B s f op) = (term59 A B s f op).
Proof. exact (fun_ext (fun g : A -> B => @lem5970261 A B g s f op)). Qed.
Lemma lem5970265 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5970266 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term60 A B s f op) = (term61 A B s f op).
Proof. exact (MK_COMB (@lem5970265 A B) (@lem5970264 A B s f op)). Qed.
Lemma lem5970271 {A B : Type'} (f : A -> B) (op : type1400 B) : (term62 A B f op) = (term63 A B f op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5970266 A B s f op)). Qed.
Lemma lem5970272 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5970273 {A B : Type'} (f : A -> B) (op : type1400 B) : (term64 A B f op) = (term65 A B f op).
Proof. exact (MK_COMB (@lem5970272 A) (@lem5970271 A B f op)). Qed.
Lemma lem5970278 {A B : Type'} (op : type1400 B) : (term66 A B op) = (term67 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5970273 A B f op)). Qed.
Lemma lem5970279 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5970280 {A B : Type'} (op : type1400 B) : (term68 A B op) = (term69 A B op).
Proof. exact (MK_COMB (@lem5970279 A B) (@lem5970278 A B op)). Qed.
Lemma lem5970285 {A B : Type'} : (term70 A B) = (term71 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5970280 A B op)). Qed.
Lemma lem5970286 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5970295 {A B : Type'} : (term72 A B) = (term73 A B).
Proof. exact (MK_COMB (@lem5970286 B) (@lem5970285 A B)). Qed.
Lemma lem5970312 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term38 A B s g x op) = (term38 A B s f x op)) = ((term38 A B s g x op) = (term38 A B s f x op)).
Proof. exact (eq_refl ((term38 A B s g x op) = (term38 A B s f x op))). Qed.
Lemma lem5970313 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term42 A B g s f op) = (term42 A B g s f op).
Proof. exact (fun_ext (fun x : A => @lem5970312 A B g s f x op)). Qed.
Lemma lem5970314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5970315 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term43 A B g s f op) = (term43 A B g s f op).
Proof. exact (MK_COMB (@lem5970314 A) (@lem5970313 A B g s f op)). Qed.
Lemma lem5970320 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term74 A B s f g x) = (term74 A B s f g x).
Proof. exact (eq_refl (term74 A B s f g x)). Qed.
Lemma lem5970321 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term75 A B s f g) = (term75 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem5970320 A B s f g x)). Qed.
Lemma lem5970322 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5970323 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term26 A B s f g) = (term26 A B s f g).
Proof. exact (MK_COMB (@lem5970322 A) (@lem5970321 A B s f g)). Qed.
Lemma lem5970324 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5970325 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term53 A B s f g) = (term53 A B s f g).
Proof. exact (MK_COMB (@lem5970324) (@lem5970323 A B s f g)). Qed.
Lemma lem5970326 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term55 A B g s f op) = (term55 A B g s f op).
Proof. exact (MK_COMB (@lem5970325 A B s f g) (@lem5970315 A B g s f op)). Qed.
Lemma lem5970329 {B : Type'} (op : type1400 B) : (term56 B op) = (term56 B op).
Proof. exact (eq_refl (term56 B op)). Qed.
Lemma lem5970330 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term57 A B g s f op) = (term57 A B g s f op).
Proof. exact (MK_COMB (@lem5970329 B op) (@lem5970326 A B g s f op)). Qed.
Lemma lem5970331 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term59 A B s f op) = (term59 A B s f op).
Proof. exact (fun_ext (fun g : A -> B => @lem5970330 A B g s f op)). Qed.
Lemma lem5970332 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5970333 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term61 A B s f op) = (term61 A B s f op).
Proof. exact (MK_COMB (@lem5970332 A B) (@lem5970331 A B s f op)). Qed.
Lemma lem5970334 {A B : Type'} (f : A -> B) (op : type1400 B) : (term63 A B f op) = (term63 A B f op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5970333 A B s f op)). Qed.
Lemma lem5970335 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5970336 {A B : Type'} (f : A -> B) (op : type1400 B) : (term65 A B f op) = (term65 A B f op).
Proof. exact (MK_COMB (@lem5970335 A) (@lem5970334 A B f op)). Qed.
Lemma lem5970337 {A B : Type'} (op : type1400 B) : (term67 A B op) = (term67 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5970336 A B f op)). Qed.
Lemma lem5970338 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5970339 {A B : Type'} (op : type1400 B) : (term69 A B op) = (term69 A B op).
Proof. exact (MK_COMB (@lem5970338 A B) (@lem5970337 A B op)). Qed.
Lemma lem5970340 {A B : Type'} : (term71 A B) = (term71 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5970339 A B op)). Qed.
Lemma lem5970341 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5970342 {A B : Type'} : (term73 A B) = (term73 A B).
Proof. exact (MK_COMB (@lem5970341 B) (@lem5970340 A B)). Qed.
Lemma lem5970391 {A B : Type'} : (term72 A B) = (term73 A B).
Proof. exact (TRANS (@lem5970295 A B) (@lem5970342 A B)). Qed.
Lemma lem5970392 {A B : Type'} : (term73 A B) = (term72 A B).
Proof. exact (SYM (@lem5970391 A B)). Qed.
Lemma lem5970394 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term26 A B s f g.
Proof. exact (h1). Qed.
Lemma lem5970396 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5970397 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term38 A B s g x op) = (term38 A B s f x op)) = (term76 A B g s f x op).
Proof. exact (@lem5970396 ((term38 A B s g x op) = (term38 A B s f x op))). Qed.
Lemma lem5970398 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term76 A B g s f x op) = ((term38 A B s g x op) = (term38 A B s f x op)).
Proof. exact (SYM (@lem5970397 A B g s f x op)). Qed.
Lemma lem5970399 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term77 A B g s f x op) : term77 A B g s f x op.
Proof. exact (h1). Qed.
Lemma lem5970412 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term74 A B s f g x) = (term78 A B s f g x).
Proof. exact (@lem17265 (@IN A x s) ((f x) = (g x))). Qed.
Lemma lem5970413 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term75 A B s f g) = (term79 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem5970412 A B s f g x)). Qed.
Lemma lem5970414 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5970467 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term26 A B s f g) = (term80 A B s f g).
Proof. exact (MK_COMB (@lem5970414 A) (@lem5970413 A B s f g)). Qed.
Lemma lem5970468 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term80 A B s f g.
Proof. exact (EQ_MP (@lem5970467 A B s f g) (@lem5970394 A B s f g h1)). Qed.
Lemma lem5970474 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) : (term81 A B g x op) = ((g x) = (@neutral B op)).
Proof. exact (@lem16933 ((g x) = (@neutral B op))). Qed.
Lemma lem5970476 {A : Type'} (x : A) (s : A -> Prop) : (term82 A x s) = (term82 A x s).
Proof. exact (eq_refl (term82 A x s)). Qed.
Lemma lem5970477 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term83 A B s g x op) = (term84 A B s g x op).
Proof. exact (MK_COMB (@lem5970476 A x s) (@lem5970474 A B g x op)). Qed.
Lemma lem5970478 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term85 A B s g x op) = (term83 A B s g x op).
Proof. exact (@lem17045 (@IN A x s) (term86 A B g x op)). Qed.
Lemma lem5970479 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term85 A B s g x op) = (term84 A B s g x op).
Proof. exact (TRANS (@lem5970478 A B s g x op) (@lem5970477 A B s g x op)). Qed.
Lemma lem5970488 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term81 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem16933 ((f x) = (@neutral B op))). Qed.
Lemma lem5970490 {A : Type'} (x : A) (s : A -> Prop) : (term82 A x s) = (term82 A x s).
Proof. exact (eq_refl (term82 A x s)). Qed.
Lemma lem5970491 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term83 A B s f x op) = (term84 A B s f x op).
Proof. exact (MK_COMB (@lem5970490 A x s) (@lem5970488 A B f x op)). Qed.
Lemma lem5970492 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term85 A B s f x op) = (term83 A B s f x op).
Proof. exact (@lem17045 (@IN A x s) (term86 A B f x op)). Qed.
Lemma lem5970493 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term85 A B s f x op) = (term84 A B s f x op).
Proof. exact (TRANS (@lem5970492 A B s f x op) (@lem5970491 A B s f x op)). Qed.
Lemma lem5970496 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term38 A B s f x op) = (term38 A B s f x op).
Proof. exact (eq_refl (term38 A B s f x op)). Qed.
Lemma lem5970497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5970498 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term87 A B s g x op) = (term88 A B s g x op).
Proof. exact (MK_COMB (@lem5970497) (@lem5970479 A B s g x op)). Qed.
Lemma lem5970499 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term89 A B g s f x op) = (term90 A B g s f x op).
Proof. exact (MK_COMB (@lem5970498 A B s g x op) (@lem5970496 A B s f x op)). Qed.
Lemma lem5970501 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (op : type1400 B) : (term91 A B s g x op) = (term91 A B s g x op).
Proof. exact (eq_refl (term91 A B s g x op)). Qed.
Lemma lem5970502 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term92 A B g s f x op) = (term93 A B g s f x op).
Proof. exact (MK_COMB (@lem5970501 A B s g x op) (@lem5970493 A B s f x op)). Qed.
Lemma lem5970503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5970504 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term94 A B g s f x op) = (term95 A B g s f x op).
Proof. exact (MK_COMB (@lem5970503) (@lem5970502 A B g s f x op)). Qed.
Lemma lem5970505 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term96 A B g s f x op) = (term97 A B g s f x op).
Proof. exact (MK_COMB (@lem5970504 A B g s f x op) (@lem5970499 A B g s f x op)). Qed.
Lemma lem5970506 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term77 A B g s f x op) = (term96 A B g s f x op).
Proof. exact (@lem17646 (term38 A B s g x op) (term38 A B s f x op)). Qed.
Lemma lem5970511 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term77 A B g s f x op) = (term97 A B g s f x op).
Proof. exact (TRANS (@lem5970506 A B g s f x op) (@lem5970505 A B g s f x op)). Qed.
Lemma lem5970535 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term78 A B s f g x) = (term78 A B s f g x).
Proof. exact (eq_refl (term78 A B s f g x)). Qed.
Lemma lem5970536 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term79 A B s f g) = (term79 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem5970535 A B s f g x)). Qed.
Lemma lem5970537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5970538 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term80 A B s f g) = (term80 A B s f g).
Proof. exact (MK_COMB (@lem5970537 A) (@lem5970536 A B s f g)). Qed.
Lemma lem5970539 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term80 A B s f g.
Proof. exact (EQ_MP (@lem5970538 A B s f g) (@lem5970468 A B s f g h1)). Qed.
Lemma lem5970625 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term77 A B g s f x op) : term97 A B g s f x op.
Proof. exact (EQ_MP (@lem5970511 A B g s f x op) (@lem5970399 A B g s f x op h1)). Qed.
Lemma lem5970626 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term93 A B g s f x op) : term93 A B g s f x op.
Proof. exact (h1). Qed.
Lemma lem5970627 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term90 A B g s f x op) : term90 A B g s f x op.
Proof. exact (h1). Qed.
Lemma lem5970628 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term93 A B g s f x op) : term84 A B s f x op.
Proof. exact (proj2 (@lem5970626 A B g s f x op h1)). Qed.
Lemma lem5970629 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term93 A B g s f x op) : term38 A B s g x op.
Proof. exact (proj1 (@lem5970626 A B g s f x op h1)). Qed.
Lemma lem5970634 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term90 A B g s f x op) : term38 A B s f x op.
Proof. exact (proj2 (@lem5970627 A B g s f x op h1)). Qed.
Lemma lem5970635 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term90 A B g s f x op) : term84 A B s g x op.
Proof. exact (proj1 (@lem5970627 A B g s f x op h1)). Qed.
Lemma lem5970668 {A : Type'} (x : A) (s : A -> Prop) (h1 : term98 A x s) : term98 A x s.
Proof. exact (h1). Qed.
Lemma lem5970680 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term78 A B s f g x) = (term78 A B s f g x).
Proof. exact (eq_refl (term78 A B s f g x)). Qed.
Lemma lem5970681 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term79 A B s f g) = (term79 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem5970680 A B s f g x)). Qed.
Lemma lem5970682 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5970684 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term80 A B s f g) = (term80 A B s f g).
Proof. exact (MK_COMB (@lem5970682 A) (@lem5970681 A B s f g)). Qed.
Lemma lem5970685 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term80 A B s f g.
Proof. exact (EQ_MP (@lem5970684 A B s f g) (@lem5970539 A B s f g h1)). Qed.
Lemma lem5970697 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : (f x) = (@neutral B op)) : (f x) = (@neutral B op).
Proof. exact (h1). Qed.
Lemma lem5970726 {A : Type'} (x : A) (s : A -> Prop) (h1 : term98 A x s) : term98 A x s.
Proof. exact (h1). Qed.
Lemma lem5970738 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term78 A B s f g x) = (term78 A B s f g x).
Proof. exact (eq_refl (term78 A B s f g x)). Qed.
Lemma lem5970739 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term79 A B s f g) = (term79 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem5970738 A B s f g x)). Qed.
Lemma lem5970740 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5970742 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term80 A B s f g) = (term80 A B s f g).
Proof. exact (MK_COMB (@lem5970740 A) (@lem5970739 A B s f g)). Qed.
Lemma lem5970743 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term80 A B s f g.
Proof. exact (EQ_MP (@lem5970742 A B s f g) (@lem5970539 A B s f g h1)). Qed.
Lemma lem5970755 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) (h1 : (g x) = (@neutral B op)) : (g x) = (@neutral B op).
Proof. exact (h1). Qed.
Lemma lem5970759 {A B : Type'} (_75675 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term99 A B s f g _75675.
Proof. exact (@lem5970685 A B s f g h1 _75675). Qed.
Lemma lem5970760 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_75675 : A) : (term99 A B s f g _75675) = (term78 A B s f g _75675).
Proof. exact (eq_refl (term99 A B s f g _75675)). Qed.
Lemma lem5970765 {A B : Type'} (_75677 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term99 A B s f g _75677.
Proof. exact (@lem5970743 A B s f g h1 _75677). Qed.
Lemma lem5970766 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_75677 : A) : (term99 A B s f g _75677) = (term78 A B s f g _75677).
Proof. exact (eq_refl (term99 A B s f g _75677)). Qed.
Lemma lem5970781 {A : Type'} (x : A) (s : A -> Prop) (h1 : term98 A x s) : term98 A x s.
Proof. exact (h1). Qed.
Lemma lem5970789 {A B : Type'} (_75675 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term78 A B s f g _75675.
Proof. exact (EQ_MP (@lem5970760 A B s f g _75675) (@lem5970759 A B _75675 s f g h1)). Qed.
Lemma lem5970793 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term93 A B g s f x op) : term86 A B g x op.
Proof. exact (proj2 (@lem5970629 A B g s f x op h1)). Qed.
Lemma lem5970795 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : (f x) = (@neutral B op)) : (f x) = (@neutral B op).
Proof. exact (h1). Qed.
Lemma lem5970809 {A : Type'} (x : A) (s : A -> Prop) (h1 : term98 A x s) : term98 A x s.
Proof. exact (h1). Qed.
Lemma lem5970817 {A B : Type'} (_75677 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term78 A B s f g _75677.
Proof. exact (EQ_MP (@lem5970766 A B s f g _75677) (@lem5970765 A B _75677 s f g h1)). Qed.
Lemma lem5970821 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term90 A B g s f x op) : term86 A B f x op.
Proof. exact (proj2 (@lem5970634 A B g s f x op h1)). Qed.
Lemma lem5970823 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) (h1 : (g x) = (@neutral B op)) : (g x) = (@neutral B op).
Proof. exact (h1). Qed.
Lemma lem5970888 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term93 A B g s f x op) : @IN A x s.
Proof. exact (proj1 (@lem5970629 A B g s f x op h1)). Qed.
Lemma lem5970889 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term93 A B g s f x op) : term100 A x s.
Proof. exact (fun h0 : term98 A x s => @lem5970888 A B g s f x op h1). Qed.
Lemma lem5970891 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5970892 {A : Type'} (x : A) (s : A -> Prop) : (term100 A x s) = (@IN A x s).
Proof. exact (@lem5970891 (@IN A x s)). Qed.
Lemma lem5970893 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term93 A B g s f x op) : @IN A x s.
Proof. exact (EQ_MP (@lem5970892 A x s) (@lem5970889 A B g s f x op h1)). Qed.
Lemma lem5970896 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5970898 {A : Type'} (x : A) (s : A -> Prop) : (term98 A x s) = (term102 A x s).
Proof. exact (@lem5970896 (@IN A x s)). Qed.
Lemma lem5970901 {A : Type'} (x : A) (s : A -> Prop) (h1 : term98 A x s) : term102 A x s.
Proof. exact (EQ_MP (@lem5970898 A x s) (@lem5970781 A x s h1)). Qed.
Lemma lem5970904 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term93 A B g s f x op) : False.
Proof. exact (@lem5970901 A x s h1 (@lem5970893 A B g s f x op h2)). Qed.
Lemma lem5970905 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term93 A B g s f x op) : term103.
Proof. exact (fun h0 : ~ False => @lem5970904 A B g s f x op h1 h2). Qed.
Lemma lem5970907 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5970908 : term103 = False.
Proof. exact (@lem5970907 False). Qed.
Lemma lem5970909 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term93 A B g s f x op) : False.
Proof. exact (EQ_MP (@lem5970908) (@lem5970905 A B g s f x op h1 h2)). Qed.
Lemma lem5970966 {B : Type'} (x : B) (y : B) (z : B) : term104 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem5970974 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term93 A B g s f x op) : @IN A x s.
Proof. exact (proj1 (@lem5970629 A B g s f x op h1)). Qed.
Lemma lem5970975 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term93 A B g s f x op) : term100 A x s.
Proof. exact (fun h0 : term98 A x s => @lem5970974 A B g s f x op h1). Qed.
Lemma lem5970977 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5970978 {A : Type'} (x : A) (s : A -> Prop) : (term100 A x s) = (@IN A x s).
Proof. exact (@lem5970977 (@IN A x s)). Qed.
Lemma lem5970979 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term93 A B g s f x op) : @IN A x s.
Proof. exact (EQ_MP (@lem5970978 A x s) (@lem5970975 A B g s f x op h1)). Qed.
Lemma lem5970985 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5970986 {A B : Type'} (f : A -> B) (g : A -> B) (_75675 : A) (s : A -> Prop) : (term78 A B s f g _75675) = (term105 A B f g _75675 s).
Proof. exact (@lem5970985 ((f _75675) = (g _75675)) (term98 A _75675 s)). Qed.
Lemma lem5970994 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5970995 {A B : Type'} (f : A -> B) (g : A -> B) (_75675 : A) (s : A -> Prop) : (term106 A B s f g _75675) = (term107 A B f g _75675 s).
Proof. exact (MK_COMB (@lem5970994) (@lem5970986 A B f g _75675 s)). Qed.
Lemma lem5971003 {A B : Type'} (f : A -> B) (g : A -> B) (_75675 : A) (s : A -> Prop) : (term105 A B f g _75675 s) = (term105 A B f g _75675 s).
Proof. exact (eq_refl (term105 A B f g _75675 s)). Qed.
Lemma lem5971004 {A B : Type'} (f : A -> B) (g : A -> B) (_75675 : A) (s : A -> Prop) : ((term78 A B s f g _75675) = (term105 A B f g _75675 s)) = ((term105 A B f g _75675 s) = (term105 A B f g _75675 s)).
Proof. exact (MK_COMB (@lem5970995 A B f g _75675 s) (@lem5971003 A B f g _75675 s)). Qed.
Lemma lem5971006 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5971007 (x : Prop) : (x = x) = True.
Proof. exact (@lem5971006 Prop x). Qed.
Lemma lem5971008 {A B : Type'} (f : A -> B) (g : A -> B) (_75675 : A) (s : A -> Prop) : ((term105 A B f g _75675 s) = (term105 A B f g _75675 s)) = True.
Proof. exact (@lem5971007 (term105 A B f g _75675 s)). Qed.
Lemma lem5971009 {A B : Type'} (f : A -> B) (g : A -> B) (_75675 : A) (s : A -> Prop) : ((term78 A B s f g _75675) = (term105 A B f g _75675 s)) = True.
Proof. exact (TRANS (@lem5971004 A B f g _75675 s) (@lem5971008 A B f g _75675 s)). Qed.
Lemma lem5971010 {A B : Type'} (f : A -> B) (g : A -> B) (_75675 : A) (s : A -> Prop) : True = ((term78 A B s f g _75675) = (term105 A B f g _75675 s)).
Proof. exact (SYM (@lem5971009 A B f g _75675 s)). Qed.
Lemma lem5971011 {A B : Type'} (f : A -> B) (g : A -> B) (_75675 : A) (s : A -> Prop) : (term78 A B s f g _75675) = (term105 A B f g _75675 s).
Proof. exact (EQ_MP (@lem5971010 A B f g _75675 s) (@lem0)). Qed.
Lemma lem5971012 {A B : Type'} (_75675 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term105 A B f g _75675 s.
Proof. exact (EQ_MP (@lem5971011 A B f g _75675 s) (@lem5970789 A B _75675 s f g h1)). Qed.
Lemma lem5971014 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5971015 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_75675 : A) : (term105 A B f g _75675 s) = (term109 A B s f g _75675).
Proof. exact (@lem5971014 (term98 A _75675 s) ((f _75675) = (g _75675))). Qed.
Lemma lem5971017 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5971018 {A : Type'} (_75675 : A) (s : A -> Prop) : (term110 A _75675 s) = (@IN A _75675 s).
Proof. exact (@lem5971017 (@IN A _75675 s)). Qed.
Lemma lem5971019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5971020 {A : Type'} (_75675 : A) (s : A -> Prop) : (term111 A _75675 s) = (term112 A _75675 s).
Proof. exact (MK_COMB (@lem5971019) (@lem5971018 A _75675 s)). Qed.
Lemma lem5971021 {A B : Type'} (f : A -> B) (g : A -> B) (_75675 : A) : ((f _75675) = (g _75675)) = ((f _75675) = (g _75675)).
Proof. exact (eq_refl ((f _75675) = (g _75675))). Qed.
Lemma lem5971022 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_75675 : A) : (term109 A B s f g _75675) = (term74 A B s f g _75675).
Proof. exact (MK_COMB (@lem5971020 A _75675 s) (@lem5971021 A B f g _75675)). Qed.
Lemma lem5971023 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_75675 : A) : (term105 A B f g _75675 s) = (term74 A B s f g _75675).
Proof. exact (TRANS (@lem5971015 A B s f g _75675) (@lem5971022 A B s f g _75675)). Qed.
Lemma lem5971026 {A B : Type'} (_75675 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term74 A B s f g _75675.
Proof. exact (EQ_MP (@lem5971023 A B s f g _75675) (@lem5971012 A B _75675 s f g h1)). Qed.
Lemma lem5971027 {A B : Type'} (_75675 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term74 A B s f g _75675.
Proof. exact (@lem5971026 A B _75675 s f g h1). Qed.
Lemma lem5971028 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term74 A B s f g x.
Proof. exact (@lem5971027 A B x s f g h1). Qed.
Lemma lem5971031 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) : (f x) = (g x).
Proof. exact (@lem5971028 A B x s f g h1 (@lem5970979 A B g s f x op h2)). Qed.
Lemma lem5971032 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) : term113 A B f g x.
Proof. exact (fun h0 : term114 A B f g x => @lem5971031 A B g s f x op h1 h2). Qed.
Lemma lem5971034 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971035 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term113 A B f g x) = ((f x) = (g x)).
Proof. exact (@lem5971034 ((f x) = (g x))). Qed.
Lemma lem5971036 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) : (f x) = (g x).
Proof. exact (EQ_MP (@lem5971035 A B f g x) (@lem5971032 A B g s f x op h1 h2)). Qed.
Lemma lem5971038 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : (f x) = (@neutral B op)) : (f x) = (@neutral B op).
Proof. exact (h1). Qed.
Lemma lem5971039 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : (f x) = (@neutral B op)) : term115 A B f x op.
Proof. exact (fun h0 : term86 A B f x op => @lem5971038 A B f x op h1). Qed.
Lemma lem5971041 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971042 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term115 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem5971041 ((f x) = (@neutral B op))). Qed.
Lemma lem5971043 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (h1 : (f x) = (@neutral B op)) : (f x) = (@neutral B op).
Proof. exact (EQ_MP (@lem5971042 A B f x op) (@lem5971039 A B f x op h1)). Qed.
Lemma lem5971061 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5971062 {B : Type'} (y : B) (x : B) (z : B) : (term116 B x y z) = (term117 B y x z).
Proof. exact (@lem5971061 (y = z) (term118 B x z)). Qed.
Lemma lem5971072 {B : Type'} (x : B) (y : B) : (term119 B x y) = (term119 B x y).
Proof. exact (eq_refl (term119 B x y)). Qed.
Lemma lem5971073 {B : Type'} (y : B) (x : B) (z : B) : (term104 B x y z) = (term120 B y x z).
Proof. exact (MK_COMB (@lem5971072 B x y) (@lem5971062 B y x z)). Qed.
Lemma lem5971077 (q : Prop) (p : Prop) (r : Prop) : (term121 p q r) = (term121 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5971078 {B : Type'} (y : B) (x : B) (z : B) : (term120 B y x z) = (term122 B y x z).
Proof. exact (@lem5971077 (y = z) (term118 B x y) (term118 B x z)). Qed.
Lemma lem5971100 {B : Type'} (y : B) (x : B) (z : B) : (term104 B x y z) = (term122 B y x z).
Proof. exact (TRANS (@lem5971073 B y x z) (@lem5971078 B y x z)). Qed.
Lemma lem5971101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5971102 {B : Type'} (y : B) (x : B) (z : B) : (term123 B x y z) = (term124 B y x z).
Proof. exact (MK_COMB (@lem5971101) (@lem5971100 B y x z)). Qed.
Lemma lem5971124 {B : Type'} (y : B) (x : B) (z : B) : (term122 B y x z) = (term122 B y x z).
Proof. exact (eq_refl (term122 B y x z)). Qed.
Lemma lem5971125 {B : Type'} (y : B) (x : B) (z : B) : ((term104 B x y z) = (term122 B y x z)) = ((term122 B y x z) = (term122 B y x z)).
Proof. exact (MK_COMB (@lem5971102 B y x z) (@lem5971124 B y x z)). Qed.
Lemma lem5971127 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5971128 (x : Prop) : (x = x) = True.
Proof. exact (@lem5971127 Prop x). Qed.
Lemma lem5971129 {B : Type'} (y : B) (x : B) (z : B) : ((term122 B y x z) = (term122 B y x z)) = True.
Proof. exact (@lem5971128 (term122 B y x z)). Qed.
Lemma lem5971130 {B : Type'} (y : B) (x : B) (z : B) : ((term104 B x y z) = (term122 B y x z)) = True.
Proof. exact (TRANS (@lem5971125 B y x z) (@lem5971129 B y x z)). Qed.
Lemma lem5971131 {B : Type'} (y : B) (x : B) (z : B) : True = ((term104 B x y z) = (term122 B y x z)).
Proof. exact (SYM (@lem5971130 B y x z)). Qed.
Lemma lem5971132 {B : Type'} (y : B) (x : B) (z : B) : (term104 B x y z) = (term122 B y x z).
Proof. exact (EQ_MP (@lem5971131 B y x z) (@lem0)). Qed.
Lemma lem5971133 {B : Type'} (y : B) (x : B) (z : B) : term122 B y x z.
Proof. exact (EQ_MP (@lem5971132 B y x z) (@lem5970966 B x y z)). Qed.
Lemma lem5971135 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5971136 {B : Type'} (x : B) (y : B) (z : B) : (term122 B y x z) = (term125 B x y z).
Proof. exact (@lem5971135 (term126 B y x z) (y = z)). Qed.
Lemma lem5971138 (a : Prop) (b : Prop) : (term127 a b) = (term128 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5971139 {B : Type'} (y : B) (x : B) (z : B) : (term129 B y x z) = (term130 B y x z).
Proof. exact (@lem5971138 (term118 B x y) (term118 B x z)). Qed.
Lemma lem5971141 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5971142 {B : Type'} (x : B) (y : B) : (term131 B x y) = (x = y).
Proof. exact (@lem5971141 (x = y)). Qed.
Lemma lem5971143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5971144 {B : Type'} (x : B) (y : B) : (term132 B x y) = (term133 B x y).
Proof. exact (MK_COMB (@lem5971143) (@lem5971142 B x y)). Qed.
Lemma lem5971146 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5971147 {B : Type'} (x : B) (z : B) : (term131 B x z) = (x = z).
Proof. exact (@lem5971146 (x = z)). Qed.
Lemma lem5971148 {B : Type'} (y : B) (x : B) (z : B) : (term130 B y x z) = (term134 B y x z).
Proof. exact (MK_COMB (@lem5971144 B x y) (@lem5971147 B x z)). Qed.
Lemma lem5971149 {B : Type'} (y : B) (x : B) (z : B) : (term129 B y x z) = (term134 B y x z).
Proof. exact (TRANS (@lem5971139 B y x z) (@lem5971148 B y x z)). Qed.
Lemma lem5971150 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5971151 {B : Type'} (y : B) (x : B) (z : B) : (term135 B y x z) = (term136 B y x z).
Proof. exact (MK_COMB (@lem5971150) (@lem5971149 B y x z)). Qed.
Lemma lem5971152 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5971153 {B : Type'} (x : B) (y : B) (z : B) : (term125 B x y z) = (term137 B x y z).
Proof. exact (MK_COMB (@lem5971151 B y x z) (@lem5971152 B y z)). Qed.
Lemma lem5971154 {B : Type'} (x : B) (y : B) (z : B) : (term122 B y x z) = (term137 B x y z).
Proof. exact (TRANS (@lem5971136 B x y z) (@lem5971153 B x y z)). Qed.
Lemma lem5971156 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : term138 A B g f x op.
Proof. exact (conj (@lem5971036 A B g s f x op h1 h2) (@lem5971043 A B f x op h3)). Qed.
Lemma lem5971158 {B : Type'} (x : B) (y : B) (z : B) : term137 B x y z.
Proof. exact (EQ_MP (@lem5971154 B x y z) (@lem5971133 B y x z)). Qed.
Lemma lem5971159 {B : Type'} (x : B) (y : B) (z : B) : term137 B x y z.
Proof. exact (@lem5971158 B x y z). Qed.
Lemma lem5971160 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) : term139 A B f g x op.
Proof. exact (@lem5971159 B (f x) (g x) (@neutral B op)). Qed.
Lemma lem5971163 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : (g x) = (@neutral B op).
Proof. exact (@lem5971160 A B f g x op (@lem5971156 A B g s f x op h1 h2 h3)). Qed.
Lemma lem5971164 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : term115 A B g x op.
Proof. exact (fun h0 : term86 A B g x op => @lem5971163 A B g s f x op h1 h2 h3). Qed.
Lemma lem5971166 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971167 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) : (term115 A B g x op) = ((g x) = (@neutral B op)).
Proof. exact (@lem5971166 ((g x) = (@neutral B op))). Qed.
Lemma lem5971168 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : (g x) = (@neutral B op).
Proof. exact (EQ_MP (@lem5971167 A B g x op) (@lem5971164 A B g s f x op h1 h2 h3)). Qed.
Lemma lem5971171 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5971173 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) : (term86 A B g x op) = (term140 A B g x op).
Proof. exact (@lem5971171 ((g x) = (@neutral B op))). Qed.
Lemma lem5971176 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term93 A B g s f x op) : term140 A B g x op.
Proof. exact (EQ_MP (@lem5971173 A B g x op) (@lem5970793 A B g s f x op h1)). Qed.
Lemma lem5971179 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : False.
Proof. exact (@lem5971176 A B g s f x op h2 (@lem5971168 A B g s f x op h1 h2 h3)). Qed.
Lemma lem5971180 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : term103.
Proof. exact (fun h0 : ~ False => @lem5971179 A B g s f x op h1 h2 h3). Qed.
Lemma lem5971182 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971183 : term103 = False.
Proof. exact (@lem5971182 False). Qed.
Lemma lem5971184 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem5971183) (@lem5971180 A B g s f x op h1 h2 h3)). Qed.
Lemma lem5971249 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term90 A B g s f x op) : @IN A x s.
Proof. exact (proj1 (@lem5970634 A B g s f x op h1)). Qed.
Lemma lem5971250 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term90 A B g s f x op) : term100 A x s.
Proof. exact (fun h0 : term98 A x s => @lem5971249 A B g s f x op h1). Qed.
Lemma lem5971252 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971253 {A : Type'} (x : A) (s : A -> Prop) : (term100 A x s) = (@IN A x s).
Proof. exact (@lem5971252 (@IN A x s)). Qed.
Lemma lem5971254 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term90 A B g s f x op) : @IN A x s.
Proof. exact (EQ_MP (@lem5971253 A x s) (@lem5971250 A B g s f x op h1)). Qed.
Lemma lem5971257 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5971259 {A : Type'} (x : A) (s : A -> Prop) : (term98 A x s) = (term102 A x s).
Proof. exact (@lem5971257 (@IN A x s)). Qed.
Lemma lem5971262 {A : Type'} (x : A) (s : A -> Prop) (h1 : term98 A x s) : term102 A x s.
Proof. exact (EQ_MP (@lem5971259 A x s) (@lem5970809 A x s h1)). Qed.
Lemma lem5971265 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term90 A B g s f x op) : False.
Proof. exact (@lem5971262 A x s h1 (@lem5971254 A B g s f x op h2)). Qed.
Lemma lem5971266 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term90 A B g s f x op) : term103.
Proof. exact (fun h0 : ~ False => @lem5971265 A B g s f x op h1 h2). Qed.
Lemma lem5971268 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971269 : term103 = False.
Proof. exact (@lem5971268 False). Qed.
Lemma lem5971270 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term90 A B g s f x op) : False.
Proof. exact (EQ_MP (@lem5971269) (@lem5971266 A B g s f x op h1 h2)). Qed.
Lemma lem5971327 {B : Type'} (x : B) (y : B) (z : B) : term104 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem5971335 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term90 A B g s f x op) : @IN A x s.
Proof. exact (proj1 (@lem5970634 A B g s f x op h1)). Qed.
Lemma lem5971336 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term90 A B g s f x op) : term100 A x s.
Proof. exact (fun h0 : term98 A x s => @lem5971335 A B g s f x op h1). Qed.
Lemma lem5971338 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971339 {A : Type'} (x : A) (s : A -> Prop) : (term100 A x s) = (@IN A x s).
Proof. exact (@lem5971338 (@IN A x s)). Qed.
Lemma lem5971340 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term90 A B g s f x op) : @IN A x s.
Proof. exact (EQ_MP (@lem5971339 A x s) (@lem5971336 A B g s f x op h1)). Qed.
Lemma lem5971346 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5971347 {A B : Type'} (f : A -> B) (g : A -> B) (_75677 : A) (s : A -> Prop) : (term78 A B s f g _75677) = (term105 A B f g _75677 s).
Proof. exact (@lem5971346 ((f _75677) = (g _75677)) (term98 A _75677 s)). Qed.
Lemma lem5971355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5971356 {A B : Type'} (f : A -> B) (g : A -> B) (_75677 : A) (s : A -> Prop) : (term106 A B s f g _75677) = (term107 A B f g _75677 s).
Proof. exact (MK_COMB (@lem5971355) (@lem5971347 A B f g _75677 s)). Qed.
Lemma lem5971364 {A B : Type'} (f : A -> B) (g : A -> B) (_75677 : A) (s : A -> Prop) : (term105 A B f g _75677 s) = (term105 A B f g _75677 s).
Proof. exact (eq_refl (term105 A B f g _75677 s)). Qed.
Lemma lem5971365 {A B : Type'} (f : A -> B) (g : A -> B) (_75677 : A) (s : A -> Prop) : ((term78 A B s f g _75677) = (term105 A B f g _75677 s)) = ((term105 A B f g _75677 s) = (term105 A B f g _75677 s)).
Proof. exact (MK_COMB (@lem5971356 A B f g _75677 s) (@lem5971364 A B f g _75677 s)). Qed.
Lemma lem5971367 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5971368 (x : Prop) : (x = x) = True.
Proof. exact (@lem5971367 Prop x). Qed.
Lemma lem5971369 {A B : Type'} (f : A -> B) (g : A -> B) (_75677 : A) (s : A -> Prop) : ((term105 A B f g _75677 s) = (term105 A B f g _75677 s)) = True.
Proof. exact (@lem5971368 (term105 A B f g _75677 s)). Qed.
Lemma lem5971370 {A B : Type'} (f : A -> B) (g : A -> B) (_75677 : A) (s : A -> Prop) : ((term78 A B s f g _75677) = (term105 A B f g _75677 s)) = True.
Proof. exact (TRANS (@lem5971365 A B f g _75677 s) (@lem5971369 A B f g _75677 s)). Qed.
Lemma lem5971371 {A B : Type'} (f : A -> B) (g : A -> B) (_75677 : A) (s : A -> Prop) : True = ((term78 A B s f g _75677) = (term105 A B f g _75677 s)).
Proof. exact (SYM (@lem5971370 A B f g _75677 s)). Qed.
Lemma lem5971372 {A B : Type'} (f : A -> B) (g : A -> B) (_75677 : A) (s : A -> Prop) : (term78 A B s f g _75677) = (term105 A B f g _75677 s).
Proof. exact (EQ_MP (@lem5971371 A B f g _75677 s) (@lem0)). Qed.
Lemma lem5971373 {A B : Type'} (_75677 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term105 A B f g _75677 s.
Proof. exact (EQ_MP (@lem5971372 A B f g _75677 s) (@lem5970817 A B _75677 s f g h1)). Qed.
Lemma lem5971375 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5971376 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_75677 : A) : (term105 A B f g _75677 s) = (term109 A B s f g _75677).
Proof. exact (@lem5971375 (term98 A _75677 s) ((f _75677) = (g _75677))). Qed.
Lemma lem5971378 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5971379 {A : Type'} (_75677 : A) (s : A -> Prop) : (term110 A _75677 s) = (@IN A _75677 s).
Proof. exact (@lem5971378 (@IN A _75677 s)). Qed.
Lemma lem5971380 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5971381 {A : Type'} (_75677 : A) (s : A -> Prop) : (term111 A _75677 s) = (term112 A _75677 s).
Proof. exact (MK_COMB (@lem5971380) (@lem5971379 A _75677 s)). Qed.
Lemma lem5971382 {A B : Type'} (f : A -> B) (g : A -> B) (_75677 : A) : ((f _75677) = (g _75677)) = ((f _75677) = (g _75677)).
Proof. exact (eq_refl ((f _75677) = (g _75677))). Qed.
Lemma lem5971383 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_75677 : A) : (term109 A B s f g _75677) = (term74 A B s f g _75677).
Proof. exact (MK_COMB (@lem5971381 A _75677 s) (@lem5971382 A B f g _75677)). Qed.
Lemma lem5971384 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_75677 : A) : (term105 A B f g _75677 s) = (term74 A B s f g _75677).
Proof. exact (TRANS (@lem5971376 A B s f g _75677) (@lem5971383 A B s f g _75677)). Qed.
Lemma lem5971387 {A B : Type'} (_75677 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term74 A B s f g _75677.
Proof. exact (EQ_MP (@lem5971384 A B s f g _75677) (@lem5971373 A B _75677 s f g h1)). Qed.
Lemma lem5971388 {A B : Type'} (_75677 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term74 A B s f g _75677.
Proof. exact (@lem5971387 A B _75677 s f g h1). Qed.
Lemma lem5971389 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term74 A B s f g x.
Proof. exact (@lem5971388 A B x s f g h1). Qed.
Lemma lem5971392 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) : (f x) = (g x).
Proof. exact (@lem5971389 A B x s f g h1 (@lem5971340 A B g s f x op h2)). Qed.
Lemma lem5971393 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) : term113 A B f g x.
Proof. exact (fun h0 : term114 A B f g x => @lem5971392 A B g s f x op h1 h2). Qed.
Lemma lem5971395 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971396 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term113 A B f g x) = ((f x) = (g x)).
Proof. exact (@lem5971395 ((f x) = (g x))). Qed.
Lemma lem5971397 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) : (f x) = (g x).
Proof. exact (EQ_MP (@lem5971396 A B f g x) (@lem5971393 A B g s f x op h1 h2)). Qed.
Lemma lem5971399 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5971400 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5971399 B x). Qed.
Lemma lem5971401 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem5971400 B (f x)). Qed.
Lemma lem5971402 {A B : Type'} (f : A -> B) (x : A) : term141 A B f x.
Proof. exact (fun h0 : term142 A B f x => @lem5971401 A B f x). Qed.
Lemma lem5971404 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971405 {A B : Type'} (f : A -> B) (x : A) : (term141 A B f x) = ((f x) = (f x)).
Proof. exact (@lem5971404 ((f x) = (f x))). Qed.
Lemma lem5971406 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem5971405 A B f x) (@lem5971402 A B f x)). Qed.
Lemma lem5971424 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5971425 {B : Type'} (y : B) (x : B) (z : B) : (term116 B x y z) = (term117 B y x z).
Proof. exact (@lem5971424 (y = z) (term118 B x z)). Qed.
Lemma lem5971435 {B : Type'} (x : B) (y : B) : (term119 B x y) = (term119 B x y).
Proof. exact (eq_refl (term119 B x y)). Qed.
Lemma lem5971436 {B : Type'} (y : B) (x : B) (z : B) : (term104 B x y z) = (term120 B y x z).
Proof. exact (MK_COMB (@lem5971435 B x y) (@lem5971425 B y x z)). Qed.
Lemma lem5971440 (q : Prop) (p : Prop) (r : Prop) : (term121 p q r) = (term121 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5971441 {B : Type'} (y : B) (x : B) (z : B) : (term120 B y x z) = (term122 B y x z).
Proof. exact (@lem5971440 (y = z) (term118 B x y) (term118 B x z)). Qed.
Lemma lem5971463 {B : Type'} (y : B) (x : B) (z : B) : (term104 B x y z) = (term122 B y x z).
Proof. exact (TRANS (@lem5971436 B y x z) (@lem5971441 B y x z)). Qed.
Lemma lem5971464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5971465 {B : Type'} (y : B) (x : B) (z : B) : (term123 B x y z) = (term124 B y x z).
Proof. exact (MK_COMB (@lem5971464) (@lem5971463 B y x z)). Qed.
Lemma lem5971487 {B : Type'} (y : B) (x : B) (z : B) : (term122 B y x z) = (term122 B y x z).
Proof. exact (eq_refl (term122 B y x z)). Qed.
Lemma lem5971488 {B : Type'} (y : B) (x : B) (z : B) : ((term104 B x y z) = (term122 B y x z)) = ((term122 B y x z) = (term122 B y x z)).
Proof. exact (MK_COMB (@lem5971465 B y x z) (@lem5971487 B y x z)). Qed.
Lemma lem5971490 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5971491 (x : Prop) : (x = x) = True.
Proof. exact (@lem5971490 Prop x). Qed.
Lemma lem5971492 {B : Type'} (y : B) (x : B) (z : B) : ((term122 B y x z) = (term122 B y x z)) = True.
Proof. exact (@lem5971491 (term122 B y x z)). Qed.
Lemma lem5971493 {B : Type'} (y : B) (x : B) (z : B) : ((term104 B x y z) = (term122 B y x z)) = True.
Proof. exact (TRANS (@lem5971488 B y x z) (@lem5971492 B y x z)). Qed.
Lemma lem5971494 {B : Type'} (y : B) (x : B) (z : B) : True = ((term104 B x y z) = (term122 B y x z)).
Proof. exact (SYM (@lem5971493 B y x z)). Qed.
Lemma lem5971495 {B : Type'} (y : B) (x : B) (z : B) : (term104 B x y z) = (term122 B y x z).
Proof. exact (EQ_MP (@lem5971494 B y x z) (@lem0)). Qed.
Lemma lem5971496 {B : Type'} (y : B) (x : B) (z : B) : term122 B y x z.
Proof. exact (EQ_MP (@lem5971495 B y x z) (@lem5971327 B x y z)). Qed.
Lemma lem5971498 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5971499 {B : Type'} (x : B) (y : B) (z : B) : (term122 B y x z) = (term125 B x y z).
Proof. exact (@lem5971498 (term126 B y x z) (y = z)). Qed.
Lemma lem5971501 (a : Prop) (b : Prop) : (term127 a b) = (term128 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5971502 {B : Type'} (y : B) (x : B) (z : B) : (term129 B y x z) = (term130 B y x z).
Proof. exact (@lem5971501 (term118 B x y) (term118 B x z)). Qed.
Lemma lem5971504 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5971505 {B : Type'} (x : B) (y : B) : (term131 B x y) = (x = y).
Proof. exact (@lem5971504 (x = y)). Qed.
Lemma lem5971506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5971507 {B : Type'} (x : B) (y : B) : (term132 B x y) = (term133 B x y).
Proof. exact (MK_COMB (@lem5971506) (@lem5971505 B x y)). Qed.
Lemma lem5971509 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5971510 {B : Type'} (x : B) (z : B) : (term131 B x z) = (x = z).
Proof. exact (@lem5971509 (x = z)). Qed.
Lemma lem5971511 {B : Type'} (y : B) (x : B) (z : B) : (term130 B y x z) = (term134 B y x z).
Proof. exact (MK_COMB (@lem5971507 B x y) (@lem5971510 B x z)). Qed.
Lemma lem5971512 {B : Type'} (y : B) (x : B) (z : B) : (term129 B y x z) = (term134 B y x z).
Proof. exact (TRANS (@lem5971502 B y x z) (@lem5971511 B y x z)). Qed.
Lemma lem5971513 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5971514 {B : Type'} (y : B) (x : B) (z : B) : (term135 B y x z) = (term136 B y x z).
Proof. exact (MK_COMB (@lem5971513) (@lem5971512 B y x z)). Qed.
Lemma lem5971515 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5971516 {B : Type'} (x : B) (y : B) (z : B) : (term125 B x y z) = (term137 B x y z).
Proof. exact (MK_COMB (@lem5971514 B y x z) (@lem5971515 B y z)). Qed.
Lemma lem5971517 {B : Type'} (x : B) (y : B) (z : B) : (term122 B y x z) = (term137 B x y z).
Proof. exact (TRANS (@lem5971499 B x y z) (@lem5971516 B x y z)). Qed.
Lemma lem5971519 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) : term143 A B g f x.
Proof. exact (conj (@lem5971397 A B g s f x op h1 h2) (@lem5971406 A B f x)). Qed.
Lemma lem5971521 {B : Type'} (x : B) (y : B) (z : B) : term137 B x y z.
Proof. exact (EQ_MP (@lem5971517 B x y z) (@lem5971496 B y x z)). Qed.
Lemma lem5971522 {B : Type'} (x : B) (y : B) (z : B) : term137 B x y z.
Proof. exact (@lem5971521 B x y z). Qed.
Lemma lem5971523 {A B : Type'} (g : A -> B) (f : A -> B) (x : A) : term144 A B g f x.
Proof. exact (@lem5971522 B (f x) (g x) (f x)). Qed.
Lemma lem5971526 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) : (g x) = (f x).
Proof. exact (@lem5971523 A B g f x (@lem5971519 A B g s f x op h1 h2)). Qed.
Lemma lem5971527 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) : term113 A B g f x.
Proof. exact (fun h0 : term114 A B g f x => @lem5971526 A B g s f x op h1 h2). Qed.
Lemma lem5971529 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971530 {A B : Type'} (g : A -> B) (f : A -> B) (x : A) : (term113 A B g f x) = ((g x) = (f x)).
Proof. exact (@lem5971529 ((g x) = (f x))). Qed.
Lemma lem5971531 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) : (g x) = (f x).
Proof. exact (EQ_MP (@lem5971530 A B g f x) (@lem5971527 A B g s f x op h1 h2)). Qed.
Lemma lem5971533 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) (h1 : (g x) = (@neutral B op)) : (g x) = (@neutral B op).
Proof. exact (h1). Qed.
Lemma lem5971534 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) (h1 : (g x) = (@neutral B op)) : term115 A B g x op.
Proof. exact (fun h0 : term86 A B g x op => @lem5971533 A B g x op h1). Qed.
Lemma lem5971536 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971537 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) : (term115 A B g x op) = ((g x) = (@neutral B op)).
Proof. exact (@lem5971536 ((g x) = (@neutral B op))). Qed.
Lemma lem5971538 {A B : Type'} (g : A -> B) (x : A) (op : type1400 B) (h1 : (g x) = (@neutral B op)) : (g x) = (@neutral B op).
Proof. exact (EQ_MP (@lem5971537 A B g x op) (@lem5971534 A B g x op h1)). Qed.
Lemma lem5971539 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : term138 A B f g x op.
Proof. exact (conj (@lem5971531 A B g s f x op h1 h2) (@lem5971538 A B g x op h3)). Qed.
Lemma lem5971541 {B : Type'} (x : B) (y : B) (z : B) : term137 B x y z.
Proof. exact (EQ_MP (@lem5971517 B x y z) (@lem5971496 B y x z)). Qed.
Lemma lem5971542 {B : Type'} (x : B) (y : B) (z : B) : term137 B x y z.
Proof. exact (@lem5971541 B x y z). Qed.
Lemma lem5971543 {A B : Type'} (g : A -> B) (f : A -> B) (x : A) (op : type1400 B) : term139 A B g f x op.
Proof. exact (@lem5971542 B (g x) (f x) (@neutral B op)). Qed.
Lemma lem5971546 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : (f x) = (@neutral B op).
Proof. exact (@lem5971543 A B g f x op (@lem5971539 A B s f g x op h1 h2 h3)). Qed.
Lemma lem5971547 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : term115 A B f x op.
Proof. exact (fun h0 : term86 A B f x op => @lem5971546 A B s f g x op h1 h2 h3). Qed.
Lemma lem5971549 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971550 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term115 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem5971549 ((f x) = (@neutral B op))). Qed.
Lemma lem5971551 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : (f x) = (@neutral B op).
Proof. exact (EQ_MP (@lem5971550 A B f x op) (@lem5971547 A B s f g x op h1 h2 h3)). Qed.
Lemma lem5971554 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5971556 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term86 A B f x op) = (term140 A B f x op).
Proof. exact (@lem5971554 ((f x) = (@neutral B op))). Qed.
Lemma lem5971559 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term90 A B g s f x op) : term140 A B f x op.
Proof. exact (EQ_MP (@lem5971556 A B f x op) (@lem5970821 A B g s f x op h1)). Qed.
Lemma lem5971562 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : False.
Proof. exact (@lem5971559 A B g s f x op h2 (@lem5971551 A B s f g x op h1 h2 h3)). Qed.
Lemma lem5971563 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : term103.
Proof. exact (fun h0 : ~ False => @lem5971562 A B s f g x op h1 h2 h3). Qed.
Lemma lem5971565 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5971566 : term103 = False.
Proof. exact (@lem5971565 False). Qed.
Lemma lem5971567 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem5971566) (@lem5971563 A B s f g x op h1 h2 h3)). Qed.
Lemma lem5971568 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : ((g x) = (@neutral B op)) = False.
Proof. exact (prop_ext (fun h4 : (g x) = (@neutral B op) => @lem5971567 A B s f g x op h1 h2 h3) (fun h4 : False => @lem5970823 A B g x op h3)). Qed.
Lemma lem5971569 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem5971568 A B s f g x op h1 h2 h3) (@lem5970823 A B g x op h3)). Qed.
Lemma lem5971570 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term90 A B g s f x op) : (term98 A x s) = False.
Proof. exact (prop_ext (fun h3 : term98 A x s => @lem5971270 A B g s f x op h1 h2) (fun h3 : False => @lem5970809 A x s h1)). Qed.
Lemma lem5971571 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term90 A B g s f x op) : False.
Proof. exact (EQ_MP (@lem5971570 A B g s f x op h1 h2) (@lem5970809 A x s h1)). Qed.
Lemma lem5971572 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : ((f x) = (@neutral B op)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (@neutral B op) => @lem5971184 A B g s f x op h1 h2 h3) (fun h4 : False => @lem5970795 A B f x op h3)). Qed.
Lemma lem5971573 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem5971572 A B g s f x op h1 h2 h3) (@lem5970795 A B f x op h3)). Qed.
Lemma lem5971574 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term93 A B g s f x op) : (term98 A x s) = False.
Proof. exact (prop_ext (fun h3 : term98 A x s => @lem5970909 A B g s f x op h1 h2) (fun h3 : False => @lem5970781 A x s h1)). Qed.
Lemma lem5971575 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term93 A B g s f x op) : False.
Proof. exact (EQ_MP (@lem5971574 A B g s f x op h1 h2) (@lem5970781 A x s h1)). Qed.
Lemma lem5971576 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : ((g x) = (@neutral B op)) = False.
Proof. exact (prop_ext (fun h4 : (g x) = (@neutral B op) => @lem5971569 A B s f g x op h1 h2 h3) (fun h4 : False => @lem5970755 A B g x op h3)). Qed.
Lemma lem5971577 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem5971576 A B s f g x op h1 h2 h3) (@lem5970755 A B g x op h3)). Qed.
Lemma lem5971578 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term90 A B g s f x op) : (term98 A x s) = False.
Proof. exact (prop_ext (fun h3 : term98 A x s => @lem5971571 A B g s f x op h1 h2) (fun h3 : False => @lem5970726 A x s h1)). Qed.
Lemma lem5971579 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term90 A B g s f x op) : False.
Proof. exact (EQ_MP (@lem5971578 A B g s f x op h1 h2) (@lem5970726 A x s h1)). Qed.
Lemma lem5971580 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : ((f x) = (@neutral B op)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (@neutral B op) => @lem5971573 A B g s f x op h1 h2 h3) (fun h4 : False => @lem5970697 A B f x op h3)). Qed.
Lemma lem5971581 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem5971580 A B g s f x op h1 h2 h3) (@lem5970697 A B f x op h3)). Qed.
Lemma lem5971582 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term93 A B g s f x op) : (term98 A x s) = False.
Proof. exact (prop_ext (fun h3 : term98 A x s => @lem5971575 A B g s f x op h1 h2) (fun h3 : False => @lem5970668 A x s h1)). Qed.
Lemma lem5971583 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term93 A B g s f x op) : False.
Proof. exact (EQ_MP (@lem5971582 A B g s f x op h1 h2) (@lem5970668 A x s h1)). Qed.
Lemma lem5971584 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : ((g x) = (@neutral B op)) = False.
Proof. exact (prop_ext (fun h4 : (g x) = (@neutral B op) => @lem5971577 A B s f g x op h1 h2 h3) (fun h4 : False => @lem5970755 A B g x op h3)). Qed.
Lemma lem5971585 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) (h3 : (g x) = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem5971584 A B s f g x op h1 h2 h3) (@lem5970755 A B g x op h3)). Qed.
Lemma lem5971586 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term90 A B g s f x op) : (term98 A x s) = False.
Proof. exact (prop_ext (fun h3 : term98 A x s => @lem5971579 A B g s f x op h1 h2) (fun h3 : False => @lem5970726 A x s h1)). Qed.
Lemma lem5971587 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term90 A B g s f x op) : False.
Proof. exact (EQ_MP (@lem5971586 A B g s f x op h1 h2) (@lem5970726 A x s h1)). Qed.
Lemma lem5971588 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : ((f x) = (@neutral B op)) = False.
Proof. exact (prop_ext (fun h4 : (f x) = (@neutral B op) => @lem5971581 A B g s f x op h1 h2 h3) (fun h4 : False => @lem5970697 A B f x op h3)). Qed.
Lemma lem5971589 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) (h3 : (f x) = (@neutral B op)) : False.
Proof. exact (EQ_MP (@lem5971588 A B g s f x op h1 h2 h3) (@lem5970697 A B f x op h3)). Qed.
Lemma lem5971590 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term93 A B g s f x op) : (term98 A x s) = False.
Proof. exact (prop_ext (fun h3 : term98 A x s => @lem5971583 A B g s f x op h1 h2) (fun h3 : False => @lem5970668 A x s h1)). Qed.
Lemma lem5971591 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term98 A x s) (h2 : term93 A B g s f x op) : False.
Proof. exact (EQ_MP (@lem5971590 A B g s f x op h1 h2) (@lem5970668 A x s h1)). Qed.
Lemma lem5971592 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term90 A B g s f x op) : False.
Proof. exact (or_elim (@lem5970635 A B g s f x op h2) (fun h0 : term98 A x s => @lem5971587 A B g s f x op h0 h2) (fun h0 : (g x) = (@neutral B op) => @lem5971585 A B s f g x op h1 h2 h0)). Qed.
Lemma lem5971593 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term93 A B g s f x op) : False.
Proof. exact (or_elim (@lem5970628 A B g s f x op h2) (fun h0 : term98 A x s => @lem5971591 A B g s f x op h0 h2) (fun h0 : (f x) = (@neutral B op) => @lem5971589 A B g s f x op h1 h2 h0)). Qed.
Lemma lem5971594 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term77 A B g s f x op) : False.
Proof. exact (or_elim (@lem5970625 A B g s f x op h2) (fun h0 : term93 A B g s f x op => @lem5971593 A B g s f x op h1 h0) (fun h0 : term90 A B g s f x op => @lem5971592 A B g s f x op h1 h0)). Qed.
Lemma lem5971595 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term77 A B g s f x op) : (term77 A B g s f x op) = False.
Proof. exact (prop_ext (fun h3 : term77 A B g s f x op => @lem5971594 A B g s f x op h1 h2) (fun h3 : False => @lem5970399 A B g s f x op h2)). Qed.
Lemma lem5971596 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term77 A B g s f x op) : False.
Proof. exact (EQ_MP (@lem5971595 A B g s f x op h1 h2) (@lem5970399 A B g s f x op h2)). Qed.
Lemma lem5971597 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term76 A B g s f x op.
Proof. exact (fun h0 : term77 A B g s f x op => @lem5971596 A B g s f x op h1 h0). Qed.
Lemma lem5971598 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : (term38 A B s g x op) = (term38 A B s f x op).
Proof. exact (EQ_MP (@lem5970398 A B g s f x op) (@lem5971597 A B x op s f g h1)). Qed.
Lemma lem5971603 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term43 A B g s f op.
Proof. exact (fun x : A => @lem5971598 A B x op s f g h1). Qed.
Lemma lem5971604 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term55 A B g s f op.
Proof. exact (fun h0 : term26 A B s f g => @lem5971603 A B op s f g h0). Qed.
Lemma lem5971605 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term57 A B g s f op.
Proof. exact (fun h0 : @monoidal B op => @lem5971604 A B g s f op). Qed.
Lemma lem5971610 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term61 A B s f op.
Proof. exact (fun g : A -> B => @lem5971605 A B g s f op). Qed.
Lemma lem5971615 {A B : Type'} (f : A -> B) (op : type1400 B) : term65 A B f op.
Proof. exact (fun s : A -> Prop => @lem5971610 A B s f op). Qed.
Lemma lem5971620 {A B : Type'} (op : type1400 B) : term69 A B op.
Proof. exact (fun f : A -> B => @lem5971615 A B f op). Qed.
Lemma lem5971625 {A B : Type'} : term73 A B.
Proof. exact (fun op : type1400 B => @lem5971620 A B op). Qed.
Lemma lem5971626 {A B : Type'} : term72 A B.
Proof. exact (EQ_MP (@lem5970392 A B) (@lem5971625 A B)). Qed.
Lemma lem5971627 {A B : Type'} (op : type1400 B) : term145 A B op.
Proof. exact (@lem5971626 A B op). Qed.
Lemma lem5971628 {A B : Type'} (op : type1400 B) : (term145 A B op) = (term68 A B op).
Proof. exact (eq_refl (term145 A B op)). Qed.
Lemma lem5971629 {A B : Type'} (op : type1400 B) : term68 A B op.
Proof. exact (EQ_MP (@lem5971628 A B op) (@lem5971627 A B op)). Qed.
Lemma lem5971630 {A B : Type'} (op : type1400 B) (f : A -> B) : term146 A B op f.
Proof. exact (@lem5971629 A B op f). Qed.
Lemma lem5971631 {A B : Type'} (f : A -> B) (op : type1400 B) : (term146 A B op f) = (term64 A B f op).
Proof. exact (eq_refl (term146 A B op f)). Qed.
Lemma lem5971632 {A B : Type'} (f : A -> B) (op : type1400 B) : term64 A B f op.
Proof. exact (EQ_MP (@lem5971631 A B f op) (@lem5971630 A B op f)). Qed.
Lemma lem5971633 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) : term147 A B f op s.
Proof. exact (@lem5971632 A B f op s). Qed.
Lemma lem5971634 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term147 A B f op s) = (term60 A B s f op).
Proof. exact (eq_refl (term147 A B f op s)). Qed.
Lemma lem5971635 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term60 A B s f op.
Proof. exact (EQ_MP (@lem5971634 A B s f op) (@lem5971633 A B f op s)). Qed.
Lemma lem5971636 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (g : A -> B) : term148 A B s f op g.
Proof. exact (@lem5971635 A B s f op g). Qed.
Lemma lem5971637 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term148 A B s f op g) = (term47 A B g s f op).
Proof. exact (eq_refl (term148 A B s f op g)). Qed.
Lemma lem5971638 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term47 A B g s f op.
Proof. exact (EQ_MP (@lem5971637 A B g s f op) (@lem5971636 A B s f op g)). Qed.
Lemma lem5971640 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term47 A B g s f op.
Proof. exact (@lem5970214 A B g s f op (@lem5971638 A B g s f op)). Qed.
Lemma lem5971641 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term54 A B g s f op.
Proof. exact (@lem5971640 A B g s f op (@lem5970116 B op h1)). Qed.
Lemma lem5971642 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : term45 A B g s f op.
Proof. exact (@lem5971641 A B g s f op h2 (@lem5970117 A B s f g h1)). Qed.
Lemma lem5971643 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) (h3 : term46 A B g s f op) : False.
Proof. exact (@lem5971642 A B s f g op h1 h2 (@lem5970198 A B g s f op h3)). Qed.
Lemma lem5971644 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) (h3 : term46 A B g s f op) : (term46 A B g s f op) = False.
Proof. exact (prop_ext (fun h4 : term46 A B g s f op => @lem5971643 A B g s f op h1 h2 h3) (fun h4 : False => @lem5970198 A B g s f op h3)). Qed.
Lemma lem5971645 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) (h3 : term46 A B g s f op) : False.
Proof. exact (EQ_MP (@lem5971644 A B g s f op h1 h2 h3) (@lem5970198 A B g s f op h3)). Qed.
Lemma lem5971646 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : term45 A B g s f op.
Proof. exact (fun h0 : term46 A B g s f op => @lem5971645 A B g s f op h1 h2 h0). Qed.
Lemma lem5971647 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : term43 A B g s f op.
Proof. exact (EQ_MP (@lem5970197 A B g s f op) (@lem5971646 A B s f g op h1 h2)). Qed.
Lemma lem5971648 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : (@support A B op g s) = (@support A B op f s).
Proof. exact (EQ_MP (@lem5970193 A B g op f s) (@lem5971647 A B s f g op h1 h2)). Qed.
Lemma lem5971649 {B : Type'} (_474 : B) (_475 : Prop) (_476 : B -> Prop) (_477 : B) : (term149 B _476 _475 _474 _477) = (term150 B _474 _475 _476 _477).
Proof. exact (@lem13473 B _474 _475 _476 _477). Qed.
Lemma lem5971650 {A B : Type'} (_474 : B) (_475 : Prop) (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (_477 : B) : (term151 A B f s g op _475 _474 _477) = (term152 A B _474 _475 f s g op _477).
Proof. exact (@lem5971649 B _474 _475 (term153 A B f s g op) _477). Qed.
Lemma lem5971651 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term154 A B g s f op) = (term155 A B f s g op).
Proof. exact (@lem5971650 A B (term156 A B op s f) (term157 A B op f s) f s g op (@neutral B op)). Qed.
Lemma lem5971652 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term158 A B f s g op) = ((@neutral B op) = (term33 A B f s g op)).
Proof. exact (eq_refl (term158 A B f s g op)). Qed.
Lemma lem5971653 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term159 A B op f s) = (term159 A B op f s).
Proof. exact (eq_refl (term159 A B op f s)). Qed.
Lemma lem5971654 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term160 A B f s g op) = (term161 A B f s g op).
Proof. exact (MK_COMB (@lem5971653 A B op f s) (@lem5971652 A B f s g op)). Qed.
Lemma lem5971655 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term162 A B g op s f) = ((term156 A B op s f) = (term33 A B f s g op)).
Proof. exact (eq_refl (term162 A B g op s f)). Qed.
Lemma lem5971656 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term163 A B op f s) = (term163 A B op f s).
Proof. exact (eq_refl (term163 A B op f s)). Qed.
Lemma lem5971657 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term164 A B g op s f) = (term165 A B f s g op).
Proof. exact (MK_COMB (@lem5971656 A B op f s) (@lem5971655 A B f s g op)). Qed.
Lemma lem5971658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5971659 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term166 A B g op s f) = (term167 A B f s g op).
Proof. exact (MK_COMB (@lem5971658) (@lem5971657 A B f s g op)). Qed.
Lemma lem5971660 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term155 A B f s g op) = (term168 A B f s g op).
Proof. exact (MK_COMB (@lem5971659 A B f s g op) (@lem5971654 A B f s g op)). Qed.
Lemma lem5971661 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term154 A B g s f op) = ((term27 A B s f op) = (term33 A B f s g op)).
Proof. exact (eq_refl (term154 A B g s f op)). Qed.
Lemma lem5971662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5971663 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term169 A B g s f op) = (term170 A B f s g op).
Proof. exact (MK_COMB (@lem5971662) (@lem5971661 A B f s g op)). Qed.
Lemma lem5971664 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term154 A B g s f op) = (term155 A B f s g op)) = (((term27 A B s f op) = (term33 A B f s g op)) = (term168 A B f s g op)).
Proof. exact (MK_COMB (@lem5971663 A B f s g op) (@lem5971660 A B f s g op)). Qed.
Lemma lem5971665 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term27 A B s f op) = (term33 A B f s g op)) = (term168 A B f s g op).
Proof. exact (EQ_MP (@lem5971664 A B f s g op) (@lem5971651 A B f s g op)). Qed.
Lemma lem5971666 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term168 A B f s g op) = ((term27 A B s f op) = (term33 A B f s g op)).
Proof. exact (SYM (@lem5971665 A B f s g op)). Qed.
Lemma lem5971667 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) : term157 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5971668 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term157 A B op f s) = ((term157 A B op f s) = True).
Proof. exact (@lem7 (term157 A B op f s)). Qed.
Lemma lem5971669 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) : (term157 A B op f s) = True.
Proof. exact (EQ_MP (@lem5971668 A B op f s) (@lem5971667 A B op f s h1)). Qed.
Lemma lem5971670 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term171 A B f s g op) = (term171 A B f s g op).
Proof. exact (eq_refl (term171 A B f s g op)). Qed.
Lemma lem5971671 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) : (term172 A B g op f s) = (term173 A B f s g op).
Proof. exact (MK_COMB (@lem5971670 A B f s g op) (@lem5971669 A B op f s h1)). Qed.
Lemma lem5971672 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term173 A B f s g op) = ((term156 A B op s f) = (term174 A B f s g op)).
Proof. exact (eq_refl (term173 A B f s g op)). Qed.
Lemma lem5971673 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term175 A B g op f s) = (term175 A B g op f s).
Proof. exact (eq_refl (term175 A B g op f s)). Qed.
Lemma lem5971674 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term172 A B g op f s) = (term173 A B f s g op)) = ((term172 A B g op f s) = ((term156 A B op s f) = (term174 A B f s g op))).
Proof. exact (MK_COMB (@lem5971673 A B g op f s) (@lem5971672 A B f s g op)). Qed.
Lemma lem5971675 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term172 A B g op f s) = ((term156 A B op s f) = (term33 A B f s g op)).
Proof. exact (eq_refl (term172 A B g op f s)). Qed.
Lemma lem5971676 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5971677 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term175 A B g op f s) = (term176 A B f s g op).
Proof. exact (MK_COMB (@lem5971676) (@lem5971675 A B f s g op)). Qed.
Lemma lem5971678 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term156 A B op s f) = (term174 A B f s g op)) = ((term156 A B op s f) = (term174 A B f s g op)).
Proof. exact (eq_refl ((term156 A B op s f) = (term174 A B f s g op))). Qed.
Lemma lem5971679 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term172 A B g op f s) = ((term156 A B op s f) = (term174 A B f s g op))) = (((term156 A B op s f) = (term33 A B f s g op)) = ((term156 A B op s f) = (term174 A B f s g op))).
Proof. exact (MK_COMB (@lem5971677 A B f s g op) (@lem5971678 A B f s g op)). Qed.
Lemma lem5971680 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term172 A B g op f s) = (term173 A B f s g op)) = (((term156 A B op s f) = (term33 A B f s g op)) = ((term156 A B op s f) = (term174 A B f s g op))).
Proof. exact (TRANS (@lem5971674 A B f s g op) (@lem5971679 A B f s g op)). Qed.
Lemma lem5971681 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) : ((term156 A B op s f) = (term33 A B f s g op)) = ((term156 A B op s f) = (term174 A B f s g op)).
Proof. exact (EQ_MP (@lem5971680 A B f s g op) (@lem5971671 A B g op f s h1)). Qed.
Lemma lem5971682 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) : ((term156 A B op s f) = (term174 A B f s g op)) = ((term156 A B op s f) = (term33 A B f s g op)).
Proof. exact (SYM (@lem5971681 A B g op f s h1)). Qed.
Lemma lem5971683 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term177 A B op f s) : term177 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5971684 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : term178 A B op f s.
Proof. exact (@lem82 (term157 A B op f s)). Qed.
Lemma lem5971685 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term177 A B op f s) : (term157 A B op f s) = False.
Proof. exact (@lem5971684 A B op f s (@lem5971683 A B op f s h1)). Qed.
Lemma lem5971686 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term179 A B f s g op) = (term179 A B f s g op).
Proof. exact (eq_refl (term179 A B f s g op)). Qed.
Lemma lem5971687 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term177 A B op f s) : (term180 A B g op f s) = (term181 A B f s g op).
Proof. exact (MK_COMB (@lem5971686 A B f s g op) (@lem5971685 A B op f s h1)). Qed.
Lemma lem5971688 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term181 A B f s g op) = ((@neutral B op) = (term182 A B f s g op)).
Proof. exact (eq_refl (term181 A B f s g op)). Qed.
Lemma lem5971689 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term183 A B g op f s) = (term183 A B g op f s).
Proof. exact (eq_refl (term183 A B g op f s)). Qed.
Lemma lem5971690 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term180 A B g op f s) = (term181 A B f s g op)) = ((term180 A B g op f s) = ((@neutral B op) = (term182 A B f s g op))).
Proof. exact (MK_COMB (@lem5971689 A B g op f s) (@lem5971688 A B f s g op)). Qed.
Lemma lem5971691 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term180 A B g op f s) = ((@neutral B op) = (term33 A B f s g op)).
Proof. exact (eq_refl (term180 A B g op f s)). Qed.
Lemma lem5971692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5971693 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term183 A B g op f s) = (term184 A B f s g op).
Proof. exact (MK_COMB (@lem5971692) (@lem5971691 A B f s g op)). Qed.
Lemma lem5971694 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((@neutral B op) = (term182 A B f s g op)) = ((@neutral B op) = (term182 A B f s g op)).
Proof. exact (eq_refl ((@neutral B op) = (term182 A B f s g op))). Qed.
Lemma lem5971695 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term180 A B g op f s) = ((@neutral B op) = (term182 A B f s g op))) = (((@neutral B op) = (term33 A B f s g op)) = ((@neutral B op) = (term182 A B f s g op))).
Proof. exact (MK_COMB (@lem5971693 A B f s g op) (@lem5971694 A B f s g op)). Qed.
Lemma lem5971696 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term180 A B g op f s) = (term181 A B f s g op)) = (((@neutral B op) = (term33 A B f s g op)) = ((@neutral B op) = (term182 A B f s g op))).
Proof. exact (TRANS (@lem5971690 A B f s g op) (@lem5971695 A B f s g op)). Qed.
Lemma lem5971697 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term177 A B op f s) : ((@neutral B op) = (term33 A B f s g op)) = ((@neutral B op) = (term182 A B f s g op)).
Proof. exact (EQ_MP (@lem5971696 A B f s g op) (@lem5971687 A B g op f s h1)). Qed.
Lemma lem5971698 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term177 A B op f s) : ((@neutral B op) = (term182 A B f s g op)) = ((@neutral B op) = (term33 A B f s g op)).
Proof. exact (SYM (@lem5971697 A B g op f s h1)). Qed.
Lemma lem5971711 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem5971712 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem5971711 B t2 t1). Qed.
Lemma lem5971713 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (g : A -> B) : (term174 A B f s g op) = (term185 A B op f s g).
Proof. exact (@lem5971712 B (@neutral B op) (term185 A B op f s g)). Qed.
Lemma lem5971714 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term186 A B op s f) = (term186 A B op s f).
Proof. exact (eq_refl (term186 A B op s f)). Qed.
Lemma lem5971715 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (g : A -> B) : ((term156 A B op s f) = (term174 A B f s g op)) = ((term156 A B op s f) = (term185 A B op f s g)).
Proof. exact (MK_COMB (@lem5971714 A B op s f) (@lem5971713 A B op f s g)). Qed.
Lemma lem5971718 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((term156 A B op s f) = (term185 A B op f s g)) = ((term156 A B op s f) = (term174 A B f s g op)).
Proof. exact (SYM (@lem5971715 A B op f s g)). Qed.
Lemma lem5971731 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5971732 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5971731 B t1 t2). Qed.
Lemma lem5971733 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (term182 A B f s g op) = (@neutral B op).
Proof. exact (@lem5971732 B (term185 A B op f s g) (@neutral B op)). Qed.
Lemma lem5971734 {B : Type'} (op : type1400 B) : (term187 B op) = (term187 B op).
Proof. exact (eq_refl (term187 B op)). Qed.
Lemma lem5971735 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((@neutral B op) = (term182 A B f s g op)) = ((@neutral B op) = (@neutral B op)).
Proof. exact (MK_COMB (@lem5971734 B op) (@lem5971733 A B f s g op)). Qed.
Lemma lem5971737 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5971738 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem5971737 B x). Qed.
Lemma lem5971739 {B : Type'} (op : type1400 B) : ((@neutral B op) = (@neutral B op)) = True.
Proof. exact (@lem5971738 B (@neutral B op)). Qed.
Lemma lem5971740 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : ((@neutral B op) = (term182 A B f s g op)) = True.
Proof. exact (TRANS (@lem5971735 A B f s g op) (@lem5971739 B op)). Qed.
Lemma lem5971741 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : True = ((@neutral B op) = (term182 A B f s g op)).
Proof. exact (SYM (@lem5971740 A B f s g op)). Qed.
Lemma lem5971742 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : (@neutral B op) = (term182 A B f s g op).
Proof. exact (EQ_MP (@lem5971741 A B f s g op) (@lem0)). Qed.
Lemma lem5971743 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term188 A B op s f g) : term188 A B op s f g.
Proof. exact (h1). Qed.
Lemma lem5971745 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5971746 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term188 A B op s f g) = (term189 A B op s f g).
Proof. exact (@lem5971745 (term188 A B op s f g)). Qed.
Lemma lem5971747 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term189 A B op s f g) = (term188 A B op s f g).
Proof. exact (SYM (@lem5971746 A B op s f g)). Qed.
Lemma lem5971748 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term190 A B op s f g) : term190 A B op s f g.
Proof. exact (h1). Qed.
Lemma lem5971749 {_119826 A : Type'} : term191 _119826 A.
Proof. exact (@lem5718201 _119826 A). Qed.
Lemma lem5971750 {A B : Type'} : term192 A B.
Proof. exact (@lem5718201 B A). Qed.
Lemma lem5971751 {_119829 B : Type'} : term192 _119829 B.
Proof. exact (@lem5718201 B _119829). Qed.
Lemma lem5971754 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term193 _119826 _119829 A B op s f g) : term193 _119826 _119829 A B op s f g.
Proof. exact (h1). Qed.
Lemma lem5971755 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : term194 _119826 _119829 A B op s f g.
Proof. exact (fun h0 : term193 _119826 _119829 A B op s f g => @lem5971754 _119826 _119829 A B op s f g h0). Qed.
Lemma lem5971756 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term194 _119826 _119829 A B op s f g) : term194 _119826 _119829 A B op s f g.
Proof. exact (h1). Qed.
Lemma lem5971757 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term193 _119826 _119829 A B op s f g) : term193 _119826 _119829 A B op s f g.
Proof. exact (h1). Qed.
Lemma lem5971758 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term193 _119826 _119829 A B op s f g) (h2 : term194 _119826 _119829 A B op s f g) : term193 _119826 _119829 A B op s f g.
Proof. exact (@lem5971756 _119826 _119829 A B op s f g h2 (@lem5971757 _119826 _119829 A B op s f g h1)). Qed.
Lemma lem5971759 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term193 _119826 _119829 A B op s f g) : term195 _119826 _119829 A B op s f g.
Proof. exact (fun h0 : term194 _119826 _119829 A B op s f g => @lem5971758 _119826 _119829 A B op s f g h1 h0). Qed.
Lemma lem5971760 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term194 _119826 _119829 A B op s f g) : term194 _119826 _119829 A B op s f g.
Proof. exact (h1). Qed.
Lemma lem5971761 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term193 _119826 _119829 A B op s f g) (h2 : term194 _119826 _119829 A B op s f g) : term193 _119826 _119829 A B op s f g.
Proof. exact (@lem5971759 _119826 _119829 A B op s f g h1 (@lem5971760 _119826 _119829 A B op s f g h2)). Qed.
Lemma lem5971762 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term194 _119826 _119829 A B op s f g) : term194 _119826 _119829 A B op s f g.
Proof. exact (fun h0 : term193 _119826 _119829 A B op s f g => @lem5971761 _119826 _119829 A B op s f g h0 h1). Qed.
Lemma lem5971763 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : term196 _119826 _119829 A B op s f g.
Proof. exact (fun h0 : term194 _119826 _119829 A B op s f g => @lem5971762 _119826 _119829 A B op s f g h0). Qed.
Lemma lem5971766 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : term194 _119826 _119829 A B op s f g.
Proof. exact (@lem5971763 _119826 _119829 A B op s f g (@lem5971755 _119826 _119829 A B op s f g)). Qed.
Lemma lem5971767 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : term194 _119826 _119829 A B op s f g.
Proof. exact (@lem5971766 _119826 _119829 A B op s f g). Qed.
Lemma lem5971847 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5971848 {A B : Type'} : (term197 A B) = (term198 A B).
Proof. exact (@lem5971847 (term192 A B)). Qed.
Lemma lem5971867 {_119829 B : Type'} : (term199 _119829 B) = (term199 _119829 B).
Proof. exact (eq_refl (term199 _119829 B)). Qed.
Lemma lem5971868 {_119829 A B : Type'} : (term200 _119829 A B) = (term201 _119829 A B).
Proof. exact (MK_COMB (@lem5971867 _119829 B) (@lem5971848 A B)). Qed.
Lemma lem5971871 {_119826 A : Type'} : (term202 _119826 A) = (term202 _119826 A).
Proof. exact (eq_refl (term202 _119826 A)). Qed.
Lemma lem5971872 {_119826 _119829 A B : Type'} : (term203 _119826 _119829 A B) = (term204 _119826 _119829 A B).
Proof. exact (MK_COMB (@lem5971871 _119826 A) (@lem5971868 _119829 A B)). Qed.
Lemma lem5971875 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term205 A B op s f g) = (term205 A B op s f g).
Proof. exact (eq_refl (term205 A B op s f g)). Qed.
Lemma lem5971876 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term206 _119826 _119829 A B op s f g) = (term207 _119826 _119829 A B op s f g).
Proof. exact (MK_COMB (@lem5971875 A B op s f g) (@lem5971872 _119826 _119829 A B)). Qed.
Lemma lem5971879 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term163 A B op f s) = (term163 A B op f s).
Proof. exact (eq_refl (term163 A B op f s)). Qed.
Lemma lem5971880 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term208 _119826 _119829 A B op s f g) = (term209 _119826 _119829 A B op s f g).
Proof. exact (MK_COMB (@lem5971879 A B op f s) (@lem5971876 _119826 _119829 A B op s f g)). Qed.
Lemma lem5971883 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term53 A B s f g) = (term53 A B s f g).
Proof. exact (eq_refl (term53 A B s f g)). Qed.
Lemma lem5971884 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term210 _119826 _119829 A B op s f g) = (term211 _119826 _119829 A B op s f g).
Proof. exact (MK_COMB (@lem5971883 A B s f g) (@lem5971880 _119826 _119829 A B op s f g)). Qed.
Lemma lem5971887 {B : Type'} (op : type1400 B) : (term56 B op) = (term56 B op).
Proof. exact (eq_refl (term56 B op)). Qed.
Lemma lem5971888 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term193 _119826 _119829 A B op s f g) = (term212 _119826 _119829 A B op s f g).
Proof. exact (MK_COMB (@lem5971887 B op) (@lem5971884 _119826 _119829 A B op s f g)). Qed.
Lemma lem5971891 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term213 _119826 _119829 A B s f g) = (term214 _119826 _119829 A B s f g).
Proof. exact (fun_ext (fun op : type1400 B => @lem5971888 _119826 _119829 A B op s f g)). Qed.
Lemma lem5971892 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5971893 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term215 _119826 _119829 A B s f g) = (term216 _119826 _119829 A B s f g).
Proof. exact (MK_COMB (@lem5971892 B) (@lem5971891 _119826 _119829 A B s f g)). Qed.
Lemma lem5971898 {_119826 _119829 A B : Type'} (f : A -> B) (g : A -> B) : (term217 _119826 _119829 A B f g) = (term218 _119826 _119829 A B f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5971893 _119826 _119829 A B s f g)). Qed.
Lemma lem5971899 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5971900 {_119826 _119829 A B : Type'} (f : A -> B) (g : A -> B) : (term219 _119826 _119829 A B f g) = (term220 _119826 _119829 A B f g).
Proof. exact (MK_COMB (@lem5971899 A) (@lem5971898 _119826 _119829 A B f g)). Qed.
Lemma lem5971905 {_119826 _119829 A B : Type'} (g : A -> B) : (term221 _119826 _119829 A B g) = (term222 _119826 _119829 A B g).
Proof. exact (fun_ext (fun f : A -> B => @lem5971900 _119826 _119829 A B f g)). Qed.
Lemma lem5971906 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5971907 {_119826 _119829 A B : Type'} (g : A -> B) : (term223 _119826 _119829 A B g) = (term224 _119826 _119829 A B g).
Proof. exact (MK_COMB (@lem5971906 A B) (@lem5971905 _119826 _119829 A B g)). Qed.
Lemma lem5971912 {_119826 _119829 A B : Type'} : (term225 _119826 _119829 A B) = (term226 _119826 _119829 A B).
Proof. exact (fun_ext (fun g : A -> B => @lem5971907 _119826 _119829 A B g)). Qed.
Lemma lem5971913 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5971922 {_119826 _119829 A B : Type'} : (term227 _119826 _119829 A B) = (term228 _119826 _119829 A B).
Proof. exact (MK_COMB (@lem5971913 A B) (@lem5971912 _119826 _119829 A B)). Qed.
Lemma lem5971933 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term37 A B x op f s) = (term38 A B s f x op)) = ((term37 A B x op f s) = (term38 A B s f x op)).
Proof. exact (eq_refl ((term37 A B x op f s) = (term38 A B s f x op))). Qed.
Lemma lem5971934 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term229 A B f x op) = (term229 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5971933 A B s f x op)). Qed.
Lemma lem5971935 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5971936 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term230 A B f x op) = (term230 A B f x op).
Proof. exact (MK_COMB (@lem5971935 A) (@lem5971934 A B f x op)). Qed.
Lemma lem5971937 {A B : Type'} (f : A -> B) (op : type1400 B) : (term231 A B f op) = (term231 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5971936 A B f x op)). Qed.
Lemma lem5971938 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5971939 {A B : Type'} (f : A -> B) (op : type1400 B) : (term232 A B f op) = (term232 A B f op).
Proof. exact (MK_COMB (@lem5971938 A) (@lem5971937 A B f op)). Qed.
Lemma lem5971940 {A B : Type'} (op : type1400 B) : (term233 A B op) = (term233 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5971939 A B f op)). Qed.
Lemma lem5971941 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5971942 {A B : Type'} (op : type1400 B) : (term234 A B op) = (term234 A B op).
Proof. exact (MK_COMB (@lem5971941 A B) (@lem5971940 A B op)). Qed.
Lemma lem5971943 {A B : Type'} : (term235 A B) = (term235 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5971942 A B op)). Qed.
Lemma lem5971944 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5971945 {A B : Type'} : (term192 A B) = (term192 A B).
Proof. exact (MK_COMB (@lem5971944 B) (@lem5971943 A B)). Qed.
Lemma lem5971946 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5971947 {A B : Type'} : (term198 A B) = (term198 A B).
Proof. exact (MK_COMB (@lem5971946) (@lem5971945 A B)). Qed.
Lemma lem5971958 {_119829 B : Type'} (s : _119829 -> Prop) (f : _119829 -> B) (x : _119829) (op : type1400 B) : ((term37 _119829 B x op f s) = (term38 _119829 B s f x op)) = ((term37 _119829 B x op f s) = (term38 _119829 B s f x op)).
Proof. exact (eq_refl ((term37 _119829 B x op f s) = (term38 _119829 B s f x op))). Qed.
Lemma lem5971959 {_119829 B : Type'} (f : _119829 -> B) (x : _119829) (op : type1400 B) : (term229 _119829 B f x op) = (term229 _119829 B f x op).
Proof. exact (fun_ext (fun s : _119829 -> Prop => @lem5971958 _119829 B s f x op)). Qed.
Lemma lem5971960 {_119829 : Type'} : (@all (_119829 -> Prop)) = (@all (_119829 -> Prop)).
Proof. exact (eq_refl (@all (_119829 -> Prop))). Qed.
Lemma lem5971961 {_119829 B : Type'} (f : _119829 -> B) (x : _119829) (op : type1400 B) : (term230 _119829 B f x op) = (term230 _119829 B f x op).
Proof. exact (MK_COMB (@lem5971960 _119829) (@lem5971959 _119829 B f x op)). Qed.
Lemma lem5971962 {_119829 B : Type'} (f : _119829 -> B) (op : type1400 B) : (term231 _119829 B f op) = (term231 _119829 B f op).
Proof. exact (fun_ext (fun x : _119829 => @lem5971961 _119829 B f x op)). Qed.
Lemma lem5971963 {_119829 : Type'} : (@all _119829) = (@all _119829).
Proof. exact (eq_refl (@all _119829)). Qed.
Lemma lem5971964 {_119829 B : Type'} (f : _119829 -> B) (op : type1400 B) : (term232 _119829 B f op) = (term232 _119829 B f op).
Proof. exact (MK_COMB (@lem5971963 _119829) (@lem5971962 _119829 B f op)). Qed.
Lemma lem5971965 {_119829 B : Type'} (op : type1400 B) : (term233 _119829 B op) = (term233 _119829 B op).
Proof. exact (fun_ext (fun f : _119829 -> B => @lem5971964 _119829 B f op)). Qed.
Lemma lem5971966 {_119829 B : Type'} : (@all (_119829 -> B)) = (@all (_119829 -> B)).
Proof. exact (eq_refl (@all (_119829 -> B))). Qed.
Lemma lem5971967 {_119829 B : Type'} (op : type1400 B) : (term234 _119829 B op) = (term234 _119829 B op).
Proof. exact (MK_COMB (@lem5971966 _119829 B) (@lem5971965 _119829 B op)). Qed.
Lemma lem5971968 {_119829 B : Type'} : (term235 _119829 B) = (term235 _119829 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5971967 _119829 B op)). Qed.
Lemma lem5971969 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5971970 {_119829 B : Type'} : (term192 _119829 B) = (term192 _119829 B).
Proof. exact (MK_COMB (@lem5971969 B) (@lem5971968 _119829 B)). Qed.
Lemma lem5971971 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5971972 {_119829 B : Type'} : (term199 _119829 B) = (term199 _119829 B).
Proof. exact (MK_COMB (@lem5971971) (@lem5971970 _119829 B)). Qed.
Lemma lem5971973 {_119829 A B : Type'} : (term201 _119829 A B) = (term201 _119829 A B).
Proof. exact (MK_COMB (@lem5971972 _119829 B) (@lem5971947 A B)). Qed.
Lemma lem5971984 {_119826 A : Type'} (s : A -> Prop) (f : A -> _119826) (x : A) (op : type1400 _119826) : ((term14 _119826 A x op f s) = (term15 _119826 A s f x op)) = ((term14 _119826 A x op f s) = (term15 _119826 A s f x op)).
Proof. exact (eq_refl ((term14 _119826 A x op f s) = (term15 _119826 A s f x op))). Qed.
Lemma lem5971985 {_119826 A : Type'} (f : A -> _119826) (x : A) (op : type1400 _119826) : (term236 _119826 A f x op) = (term236 _119826 A f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5971984 _119826 A s f x op)). Qed.
Lemma lem5971986 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5971987 {_119826 A : Type'} (f : A -> _119826) (x : A) (op : type1400 _119826) : (term12 _119826 A f x op) = (term12 _119826 A f x op).
Proof. exact (MK_COMB (@lem5971986 A) (@lem5971985 _119826 A f x op)). Qed.
Lemma lem5971988 {_119826 A : Type'} (f : A -> _119826) (op : type1400 _119826) : (term237 _119826 A f op) = (term237 _119826 A f op).
Proof. exact (fun_ext (fun x : A => @lem5971987 _119826 A f x op)). Qed.
Lemma lem5971989 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5971990 {_119826 A : Type'} (f : A -> _119826) (op : type1400 _119826) : (term10 _119826 A f op) = (term10 _119826 A f op).
Proof. exact (MK_COMB (@lem5971989 A) (@lem5971988 _119826 A f op)). Qed.
Lemma lem5971991 {_119826 A : Type'} (op : type1400 _119826) : (term238 _119826 A op) = (term238 _119826 A op).
Proof. exact (fun_ext (fun f : A -> _119826 => @lem5971990 _119826 A f op)). Qed.
Lemma lem5971992 {_119826 A : Type'} : (@all (A -> _119826)) = (@all (A -> _119826)).
Proof. exact (eq_refl (@all (A -> _119826))). Qed.
Lemma lem5971993 {_119826 A : Type'} (op : type1400 _119826) : (term8 _119826 A op) = (term8 _119826 A op).
Proof. exact (MK_COMB (@lem5971992 _119826 A) (@lem5971991 _119826 A op)). Qed.
Lemma lem5971994 {_119826 A : Type'} : (term239 _119826 A) = (term239 _119826 A).
Proof. exact (fun_ext (fun op : type1400 _119826 => @lem5971993 _119826 A op)). Qed.
Lemma lem5971995 {_119826 : Type'} : (@all (_119826 -> _119826 -> _119826)) = (@all (_119826 -> _119826 -> _119826)).
Proof. exact (eq_refl (@all (_119826 -> _119826 -> _119826))). Qed.
Lemma lem5971996 {_119826 A : Type'} : (term191 _119826 A) = (term191 _119826 A).
Proof. exact (MK_COMB (@lem5971995 _119826) (@lem5971994 _119826 A)). Qed.
Lemma lem5971997 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5971998 {_119826 A : Type'} : (term202 _119826 A) = (term202 _119826 A).
Proof. exact (MK_COMB (@lem5971997) (@lem5971996 _119826 A)). Qed.
Lemma lem5971999 {_119826 _119829 A B : Type'} : (term204 _119826 _119829 A B) = (term204 _119826 _119829 A B).
Proof. exact (MK_COMB (@lem5971998 _119826 A) (@lem5971973 _119829 A B)). Qed.
Lemma lem5972004 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term240 A B op s f g x) = (term240 A B op s f g x).
Proof. exact (eq_refl (term240 A B op s f g x)). Qed.
Lemma lem5972005 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term241 A B op s f g) = (term241 A B op s f g).
Proof. exact (fun_ext (fun x : A => @lem5972004 A B op s f g x)). Qed.
Lemma lem5972006 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5972007 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term242 A B op s f g) = (term242 A B op s f g).
Proof. exact (MK_COMB (@lem5972006 A) (@lem5972005 A B op s f g)). Qed.
Lemma lem5972010 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term243 A B op f s) = (term243 A B op f s).
Proof. exact (eq_refl (term243 A B op f s)). Qed.
Lemma lem5972011 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term188 A B op s f g) = (term188 A B op s f g).
Proof. exact (MK_COMB (@lem5972010 A B op f s) (@lem5972007 A B op s f g)). Qed.
Lemma lem5972012 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5972013 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term190 A B op s f g) = (term190 A B op s f g).
Proof. exact (MK_COMB (@lem5972012) (@lem5972011 A B op s f g)). Qed.
Lemma lem5972014 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5972015 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term205 A B op s f g) = (term205 A B op s f g).
Proof. exact (MK_COMB (@lem5972014) (@lem5972013 A B op s f g)). Qed.
Lemma lem5972016 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term207 _119826 _119829 A B op s f g) = (term207 _119826 _119829 A B op s f g).
Proof. exact (MK_COMB (@lem5972015 A B op s f g) (@lem5971999 _119826 _119829 A B)). Qed.
Lemma lem5972019 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term163 A B op f s) = (term163 A B op f s).
Proof. exact (eq_refl (term163 A B op f s)). Qed.
Lemma lem5972020 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term209 _119826 _119829 A B op s f g) = (term209 _119826 _119829 A B op s f g).
Proof. exact (MK_COMB (@lem5972019 A B op f s) (@lem5972016 _119826 _119829 A B op s f g)). Qed.
Lemma lem5972025 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term74 A B s f g x) = (term74 A B s f g x).
Proof. exact (eq_refl (term74 A B s f g x)). Qed.
Lemma lem5972026 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term75 A B s f g) = (term75 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem5972025 A B s f g x)). Qed.
Lemma lem5972027 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5972028 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term26 A B s f g) = (term26 A B s f g).
Proof. exact (MK_COMB (@lem5972027 A) (@lem5972026 A B s f g)). Qed.
Lemma lem5972029 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5972030 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term53 A B s f g) = (term53 A B s f g).
Proof. exact (MK_COMB (@lem5972029) (@lem5972028 A B s f g)). Qed.
Lemma lem5972031 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term211 _119826 _119829 A B op s f g) = (term211 _119826 _119829 A B op s f g).
Proof. exact (MK_COMB (@lem5972030 A B s f g) (@lem5972020 _119826 _119829 A B op s f g)). Qed.
Lemma lem5972034 {B : Type'} (op : type1400 B) : (term56 B op) = (term56 B op).
Proof. exact (eq_refl (term56 B op)). Qed.
Lemma lem5972035 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term212 _119826 _119829 A B op s f g) = (term212 _119826 _119829 A B op s f g).
Proof. exact (MK_COMB (@lem5972034 B op) (@lem5972031 _119826 _119829 A B op s f g)). Qed.
Lemma lem5972036 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term214 _119826 _119829 A B s f g) = (term214 _119826 _119829 A B s f g).
Proof. exact (fun_ext (fun op : type1400 B => @lem5972035 _119826 _119829 A B op s f g)). Qed.
Lemma lem5972037 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5972038 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term216 _119826 _119829 A B s f g) = (term216 _119826 _119829 A B s f g).
Proof. exact (MK_COMB (@lem5972037 B) (@lem5972036 _119826 _119829 A B s f g)). Qed.
Lemma lem5972039 {_119826 _119829 A B : Type'} (f : A -> B) (g : A -> B) : (term218 _119826 _119829 A B f g) = (term218 _119826 _119829 A B f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5972038 _119826 _119829 A B s f g)). Qed.
Lemma lem5972040 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5972041 {_119826 _119829 A B : Type'} (f : A -> B) (g : A -> B) : (term220 _119826 _119829 A B f g) = (term220 _119826 _119829 A B f g).
Proof. exact (MK_COMB (@lem5972040 A) (@lem5972039 _119826 _119829 A B f g)). Qed.
Lemma lem5972042 {_119826 _119829 A B : Type'} (g : A -> B) : (term222 _119826 _119829 A B g) = (term222 _119826 _119829 A B g).
Proof. exact (fun_ext (fun f : A -> B => @lem5972041 _119826 _119829 A B f g)). Qed.
Lemma lem5972043 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5972044 {_119826 _119829 A B : Type'} (g : A -> B) : (term224 _119826 _119829 A B g) = (term224 _119826 _119829 A B g).
Proof. exact (MK_COMB (@lem5972043 A B) (@lem5972042 _119826 _119829 A B g)). Qed.
Lemma lem5972045 {_119826 _119829 A B : Type'} : (term226 _119826 _119829 A B) = (term226 _119826 _119829 A B).
Proof. exact (fun_ext (fun g : A -> B => @lem5972044 _119826 _119829 A B g)). Qed.
Lemma lem5972046 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5972047 {_119826 _119829 A B : Type'} : (term228 _119826 _119829 A B) = (term228 _119826 _119829 A B).
Proof. exact (MK_COMB (@lem5972046 A B) (@lem5972045 _119826 _119829 A B)). Qed.
Lemma lem5972182 {_119826 _119829 A B : Type'} : (term227 _119826 _119829 A B) = (term228 _119826 _119829 A B).
Proof. exact (TRANS (@lem5971922 _119826 _119829 A B) (@lem5972047 _119826 _119829 A B)). Qed.
Lemma lem5972183 {_119826 _119829 A B : Type'} : (term228 _119826 _119829 A B) = (term227 _119826 _119829 A B).
Proof. exact (SYM (@lem5972182 _119826 _119829 A B)). Qed.
Lemma lem5972185 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term26 A B s f g.
Proof. exact (h1). Qed.
Lemma lem5972187 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term190 A B op s f g) : term190 A B op s f g.
Proof. exact (h1). Qed.
Lemma lem5972190 {A B : Type'} (h1 : term192 A B) : term192 A B.
Proof. exact (h1). Qed.
Lemma lem5972203 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term74 A B s f g x) = (term78 A B s f g x).
Proof. exact (@lem17265 (@IN A x s) ((f x) = (g x))). Qed.
Lemma lem5972204 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term75 A B s f g) = (term79 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem5972203 A B s f g x)). Qed.
Lemma lem5972205 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5972258 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term26 A B s f g) = (term80 A B s f g).
Proof. exact (MK_COMB (@lem5972205 A) (@lem5972204 A B s f g)). Qed.
Lemma lem5972259 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term80 A B s f g.
Proof. exact (EQ_MP (@lem5972258 A B s f g) (@lem5972185 A B s f g h1)). Qed.
Lemma lem5972265 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) : term157 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5972273 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term244 A B op s f g x) = (term245 A B op s f g x).
Proof. exact (@lem17362 (term37 A B x op f s) ((f x) = (g x))). Qed.
Lemma lem5972274 {A : Type'} (P : A -> Prop) : (term246 A P) = (term247 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5972275 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term248 A B op s f g) = (term249 A B op s f g).
Proof. exact (@lem5972274 A (term241 A B op s f g)). Qed.
Lemma lem5972276 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term250 A B op s f g x) = (term240 A B op s f g x).
Proof. exact (eq_refl (term250 A B op s f g x)). Qed.
Lemma lem5972277 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5972278 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term251 A B op s f g x) = (term244 A B op s f g x).
Proof. exact (MK_COMB (@lem5972277) (@lem5972276 A B op s f g x)). Qed.
Lemma lem5972279 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term251 A B op s f g x) = (term245 A B op s f g x).
Proof. exact (TRANS (@lem5972278 A B op s f g x) (@lem5972273 A B op s f g x)). Qed.
Lemma lem5972280 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term252 A B op s f g) = (term253 A B op s f g).
Proof. exact (fun_ext (fun x : A => @lem5972279 A B op s f g x)). Qed.
Lemma lem5972281 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5972282 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term249 A B op s f g) = (term254 A B op s f g).
Proof. exact (MK_COMB (@lem5972281 A) (@lem5972280 A B op s f g)). Qed.
Lemma lem5972283 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term248 A B op s f g) = (term254 A B op s f g).
Proof. exact (TRANS (@lem5972275 A B op s f g) (@lem5972282 A B op s f g)). Qed.
Lemma lem5972285 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term255 A B op f s) = (term255 A B op f s).
Proof. exact (eq_refl (term255 A B op f s)). Qed.
Lemma lem5972286 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term256 A B op s f g) = (term257 A B op s f g).
Proof. exact (MK_COMB (@lem5972285 A B op f s) (@lem5972283 A B op s f g)). Qed.
Lemma lem5972287 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term190 A B op s f g) = (term256 A B op s f g).
Proof. exact (@lem17045 (term157 A B op f s) (term242 A B op s f g)). Qed.
Lemma lem5972288 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term190 A B op s f g) = (term257 A B op s f g).
Proof. exact (TRANS (@lem5972287 A B op s f g) (@lem5972286 A B op s f g)). Qed.
Lemma lem5972339 {A : Type'} (P : Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5972340 {A : Type'} (P : Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (@lem5972339 A P Q). Qed.
Lemma lem5972341 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term260 A B op s f g) = (term261 A B op s f g).
Proof. exact (@lem5972340 A (term177 A B op f s) (term253 A B op s f g)). Qed.
Lemma lem5972342 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term262 A B op s f g x) = (term245 A B op s f g x).
Proof. exact (eq_refl (term262 A B op s f g x)). Qed.
Lemma lem5972343 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term263 A B op s f g) = (term253 A B op s f g).
Proof. exact (fun_ext (fun x : A => @lem5972342 A B op s f g x)). Qed.
Lemma lem5972344 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5972345 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term264 A B op s f g) = (term254 A B op s f g).
Proof. exact (MK_COMB (@lem5972344 A) (@lem5972343 A B op s f g)). Qed.
Lemma lem5972346 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term255 A B op f s) = (term255 A B op f s).
Proof. exact (eq_refl (term255 A B op f s)). Qed.
Lemma lem5972347 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term260 A B op s f g) = (term257 A B op s f g).
Proof. exact (MK_COMB (@lem5972346 A B op f s) (@lem5972345 A B op s f g)). Qed.
Lemma lem5972348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5972349 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term265 A B op s f g) = (term266 A B op s f g).
Proof. exact (MK_COMB (@lem5972348) (@lem5972347 A B op s f g)). Qed.
Lemma lem5972350 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term262 A B op s f g x) = (term245 A B op s f g x).
Proof. exact (eq_refl (term262 A B op s f g x)). Qed.
Lemma lem5972351 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term255 A B op f s) = (term255 A B op f s).
Proof. exact (eq_refl (term255 A B op f s)). Qed.
Lemma lem5972352 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term267 A B op s f g x) = (term268 A B op s f g x).
Proof. exact (MK_COMB (@lem5972351 A B op f s) (@lem5972350 A B op s f g x)). Qed.
Lemma lem5972353 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term269 A B op s f g) = (term270 A B op s f g).
Proof. exact (fun_ext (fun x : A => @lem5972352 A B op s f g x)). Qed.
Lemma lem5972354 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5972355 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term261 A B op s f g) = (term271 A B op s f g).
Proof. exact (MK_COMB (@lem5972354 A) (@lem5972353 A B op s f g)). Qed.
Lemma lem5972356 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term260 A B op s f g) = (term261 A B op s f g)) = ((term257 A B op s f g) = (term271 A B op s f g)).
Proof. exact (MK_COMB (@lem5972349 A B op s f g) (@lem5972355 A B op s f g)). Qed.
Lemma lem5972358 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term257 A B op s f g) = (term271 A B op s f g).
Proof. exact (EQ_MP (@lem5972356 A B op s f g) (@lem5972341 A B op s f g)). Qed.
Lemma lem5972359 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term190 A B op s f g) = (term271 A B op s f g).
Proof. exact (TRANS (@lem5972288 A B op s f g) (@lem5972358 A B op s f g)). Qed.
Lemma lem5972360 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term190 A B op s f g) : term271 A B op s f g.
Proof. exact (EQ_MP (@lem5972359 A B op s f g) (@lem5972187 A B op s f g h1)). Qed.
Lemma lem5973582 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term81 A B f x op) = ((f x) = (@neutral B op)).
Proof. exact (@lem16933 ((f x) = (@neutral B op))). Qed.
Lemma lem5973584 {A : Type'} (x : A) (s : A -> Prop) : (term82 A x s) = (term82 A x s).
Proof. exact (eq_refl (term82 A x s)). Qed.
Lemma lem5973585 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term83 A B s f x op) = (term84 A B s f x op).
Proof. exact (MK_COMB (@lem5973584 A x s) (@lem5973582 A B f x op)). Qed.
Lemma lem5973586 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term85 A B s f x op) = (term83 A B s f x op).
Proof. exact (@lem17045 (@IN A x s) (term86 A B f x op)). Qed.
Lemma lem5973587 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term85 A B s f x op) = (term84 A B s f x op).
Proof. exact (TRANS (@lem5973586 A B s f x op) (@lem5973585 A B s f x op)). Qed.
Lemma lem5973593 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term272 A B s f x op) = (term272 A B s f x op).
Proof. exact (eq_refl (term272 A B s f x op)). Qed.
Lemma lem5973595 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term273 A B x op f s) = (term273 A B x op f s).
Proof. exact (eq_refl (term273 A B x op f s)). Qed.
Lemma lem5973596 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term274 A B s f x op) = (term275 A B s f x op).
Proof. exact (MK_COMB (@lem5973595 A B x op f s) (@lem5973587 A B s f x op)). Qed.
Lemma lem5973597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5973598 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term276 A B s f x op) = (term277 A B s f x op).
Proof. exact (MK_COMB (@lem5973597) (@lem5973596 A B s f x op)). Qed.
Lemma lem5973599 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term278 A B s f x op) = (term279 A B s f x op).
Proof. exact (MK_COMB (@lem5973598 A B s f x op) (@lem5973593 A B s f x op)). Qed.
Lemma lem5973600 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term37 A B x op f s) = (term38 A B s f x op)) = (term278 A B s f x op).
Proof. exact (@lem17784 (term37 A B x op f s) (term38 A B s f x op)). Qed.
Lemma lem5973601 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : ((term37 A B x op f s) = (term38 A B s f x op)) = (term279 A B s f x op).
Proof. exact (TRANS (@lem5973600 A B s f x op) (@lem5973599 A B s f x op)). Qed.
Lemma lem5973602 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term229 A B f x op) = (term280 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5973601 A B s f x op)). Qed.
Lemma lem5973603 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5973604 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term230 A B f x op) = (term281 A B f x op).
Proof. exact (MK_COMB (@lem5973603 A) (@lem5973602 A B f x op)). Qed.
Lemma lem5973605 {A B : Type'} (f : A -> B) (op : type1400 B) : (term231 A B f op) = (term282 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5973604 A B f x op)). Qed.
Lemma lem5973606 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5973607 {A B : Type'} (f : A -> B) (op : type1400 B) : (term232 A B f op) = (term283 A B f op).
Proof. exact (MK_COMB (@lem5973606 A) (@lem5973605 A B f op)). Qed.
Lemma lem5973608 {A B : Type'} (op : type1400 B) : (term233 A B op) = (term284 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5973607 A B f op)). Qed.
Lemma lem5973609 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5973610 {A B : Type'} (op : type1400 B) : (term234 A B op) = (term285 A B op).
Proof. exact (MK_COMB (@lem5973609 A B) (@lem5973608 A B op)). Qed.
Lemma lem5973611 {A B : Type'} : (term235 A B) = (term286 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5973610 A B op)). Qed.
Lemma lem5973612 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5973613 {A B : Type'} : (term192 A B) = (term287 A B).
Proof. exact (MK_COMB (@lem5973612 B) (@lem5973611 A B)). Qed.
Lemma lem5973627 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term288 A P Q) = (term289 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5973628 {A : Type'} (P : type686 A) (Q : type686 A) : (term290 A P Q) = (term291 A P Q).
Proof. exact (@lem5973627 (A -> Prop) P Q). Qed.
Lemma lem5973629 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term292 A B f x op) = (term293 A B f x op).
Proof. exact (@lem5973628 A (term294 A B f x op) (term295 A B f x op)). Qed.
Lemma lem5973630 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term296 A B f x op s) = (term275 A B s f x op).
Proof. exact (eq_refl (term296 A B f x op s)). Qed.
Lemma lem5973631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5973632 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term297 A B f x op s) = (term277 A B s f x op).
Proof. exact (MK_COMB (@lem5973631) (@lem5973630 A B s f x op)). Qed.
Lemma lem5973633 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term298 A B f x op s) = (term272 A B s f x op).
Proof. exact (eq_refl (term298 A B f x op s)). Qed.
Lemma lem5973634 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term299 A B f x op s) = (term279 A B s f x op).
Proof. exact (MK_COMB (@lem5973632 A B s f x op) (@lem5973633 A B s f x op)). Qed.
Lemma lem5973635 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term300 A B f x op) = (term280 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5973634 A B s f x op)). Qed.
Lemma lem5973636 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5973637 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term292 A B f x op) = (term281 A B f x op).
Proof. exact (MK_COMB (@lem5973636 A) (@lem5973635 A B f x op)). Qed.
Lemma lem5973638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5973639 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term301 A B f x op) = (term302 A B f x op).
Proof. exact (MK_COMB (@lem5973638) (@lem5973637 A B f x op)). Qed.
Lemma lem5973640 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term296 A B f x op s) = (term275 A B s f x op).
Proof. exact (eq_refl (term296 A B f x op s)). Qed.
Lemma lem5973641 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term303 A B f x op) = (term294 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5973640 A B s f x op)). Qed.
Lemma lem5973642 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5973643 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term304 A B f x op) = (term305 A B f x op).
Proof. exact (MK_COMB (@lem5973642 A) (@lem5973641 A B f x op)). Qed.
Lemma lem5973644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5973645 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term306 A B f x op) = (term307 A B f x op).
Proof. exact (MK_COMB (@lem5973644) (@lem5973643 A B f x op)). Qed.
Lemma lem5973646 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term298 A B f x op s) = (term272 A B s f x op).
Proof. exact (eq_refl (term298 A B f x op s)). Qed.
Lemma lem5973647 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term308 A B f x op) = (term295 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5973646 A B s f x op)). Qed.
Lemma lem5973648 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5973649 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term309 A B f x op) = (term310 A B f x op).
Proof. exact (MK_COMB (@lem5973648 A) (@lem5973647 A B f x op)). Qed.
Lemma lem5973650 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term293 A B f x op) = (term311 A B f x op).
Proof. exact (MK_COMB (@lem5973645 A B f x op) (@lem5973649 A B f x op)). Qed.
Lemma lem5973651 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : ((term292 A B f x op) = (term293 A B f x op)) = ((term281 A B f x op) = (term311 A B f x op)).
Proof. exact (MK_COMB (@lem5973639 A B f x op) (@lem5973650 A B f x op)). Qed.
Lemma lem5973652 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term281 A B f x op) = (term311 A B f x op).
Proof. exact (EQ_MP (@lem5973651 A B f x op) (@lem5973629 A B f x op)). Qed.
Lemma lem5973749 {A B : Type'} (f : A -> B) (op : type1400 B) : (term282 A B f op) = (term312 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5973652 A B f x op)). Qed.
Lemma lem5973750 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5973751 {A B : Type'} (f : A -> B) (op : type1400 B) : (term283 A B f op) = (term313 A B f op).
Proof. exact (MK_COMB (@lem5973750 A) (@lem5973749 A B f op)). Qed.
Lemma lem5973753 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term288 A P Q) = (term289 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5973754 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term288 A P Q) = (term289 A P Q).
Proof. exact (@lem5973753 A P Q). Qed.
Lemma lem5973755 {A B : Type'} (f : A -> B) (op : type1400 B) : (term314 A B f op) = (term315 A B f op).
Proof. exact (@lem5973754 A (term316 A B f op) (term317 A B f op)). Qed.
Lemma lem5973756 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term318 A B f op x) = (term305 A B f x op).
Proof. exact (eq_refl (term318 A B f op x)). Qed.
Lemma lem5973757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5973758 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term319 A B f op x) = (term307 A B f x op).
Proof. exact (MK_COMB (@lem5973757) (@lem5973756 A B f x op)). Qed.
Lemma lem5973759 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term320 A B f op x) = (term310 A B f x op).
Proof. exact (eq_refl (term320 A B f op x)). Qed.
Lemma lem5973760 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term321 A B f op x) = (term311 A B f x op).
Proof. exact (MK_COMB (@lem5973758 A B f x op) (@lem5973759 A B f x op)). Qed.
Lemma lem5973761 {A B : Type'} (f : A -> B) (op : type1400 B) : (term322 A B f op) = (term312 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5973760 A B f x op)). Qed.
Lemma lem5973762 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5973763 {A B : Type'} (f : A -> B) (op : type1400 B) : (term314 A B f op) = (term313 A B f op).
Proof. exact (MK_COMB (@lem5973762 A) (@lem5973761 A B f op)). Qed.
Lemma lem5973764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5973765 {A B : Type'} (f : A -> B) (op : type1400 B) : (term323 A B f op) = (term324 A B f op).
Proof. exact (MK_COMB (@lem5973764) (@lem5973763 A B f op)). Qed.
Lemma lem5973766 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term318 A B f op x) = (term305 A B f x op).
Proof. exact (eq_refl (term318 A B f op x)). Qed.
Lemma lem5973767 {A B : Type'} (f : A -> B) (op : type1400 B) : (term325 A B f op) = (term316 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5973766 A B f x op)). Qed.
Lemma lem5973768 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5973769 {A B : Type'} (f : A -> B) (op : type1400 B) : (term326 A B f op) = (term327 A B f op).
Proof. exact (MK_COMB (@lem5973768 A) (@lem5973767 A B f op)). Qed.
Lemma lem5973770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5973771 {A B : Type'} (f : A -> B) (op : type1400 B) : (term328 A B f op) = (term329 A B f op).
Proof. exact (MK_COMB (@lem5973770) (@lem5973769 A B f op)). Qed.
Lemma lem5973772 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term320 A B f op x) = (term310 A B f x op).
Proof. exact (eq_refl (term320 A B f op x)). Qed.
Lemma lem5973773 {A B : Type'} (f : A -> B) (op : type1400 B) : (term330 A B f op) = (term317 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5973772 A B f x op)). Qed.
Lemma lem5973774 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5973775 {A B : Type'} (f : A -> B) (op : type1400 B) : (term331 A B f op) = (term332 A B f op).
Proof. exact (MK_COMB (@lem5973774 A) (@lem5973773 A B f op)). Qed.
Lemma lem5973776 {A B : Type'} (f : A -> B) (op : type1400 B) : (term315 A B f op) = (term333 A B f op).
Proof. exact (MK_COMB (@lem5973771 A B f op) (@lem5973775 A B f op)). Qed.
Lemma lem5973777 {A B : Type'} (f : A -> B) (op : type1400 B) : ((term314 A B f op) = (term315 A B f op)) = ((term313 A B f op) = (term333 A B f op)).
Proof. exact (MK_COMB (@lem5973765 A B f op) (@lem5973776 A B f op)). Qed.
Lemma lem5973778 {A B : Type'} (f : A -> B) (op : type1400 B) : (term313 A B f op) = (term333 A B f op).
Proof. exact (EQ_MP (@lem5973777 A B f op) (@lem5973755 A B f op)). Qed.
Lemma lem5973883 {A B : Type'} (f : A -> B) (op : type1400 B) : (term283 A B f op) = (term333 A B f op).
Proof. exact (TRANS (@lem5973751 A B f op) (@lem5973778 A B f op)). Qed.
Lemma lem5973884 {A B : Type'} (op : type1400 B) : (term284 A B op) = (term334 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5973883 A B f op)). Qed.
Lemma lem5973885 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5973886 {A B : Type'} (op : type1400 B) : (term285 A B op) = (term335 A B op).
Proof. exact (MK_COMB (@lem5973885 A B) (@lem5973884 A B op)). Qed.
Lemma lem5973888 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term288 A P Q) = (term289 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5973889 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term336 A B P Q) = (term337 A B P Q).
Proof. exact (@lem5973888 (A -> B) P Q). Qed.
Lemma lem5973890 {A B : Type'} (op : type1400 B) : (term338 A B op) = (term339 A B op).
Proof. exact (@lem5973889 A B (term340 A B op) (term341 A B op)). Qed.
Lemma lem5973891 {A B : Type'} (f : A -> B) (op : type1400 B) : (term342 A B op f) = (term327 A B f op).
Proof. exact (eq_refl (term342 A B op f)). Qed.
Lemma lem5973892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5973893 {A B : Type'} (f : A -> B) (op : type1400 B) : (term343 A B op f) = (term329 A B f op).
Proof. exact (MK_COMB (@lem5973892) (@lem5973891 A B f op)). Qed.
Lemma lem5973894 {A B : Type'} (f : A -> B) (op : type1400 B) : (term344 A B op f) = (term332 A B f op).
Proof. exact (eq_refl (term344 A B op f)). Qed.
Lemma lem5973895 {A B : Type'} (f : A -> B) (op : type1400 B) : (term345 A B op f) = (term333 A B f op).
Proof. exact (MK_COMB (@lem5973893 A B f op) (@lem5973894 A B f op)). Qed.
Lemma lem5973896 {A B : Type'} (op : type1400 B) : (term346 A B op) = (term334 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5973895 A B f op)). Qed.
Lemma lem5973897 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5973898 {A B : Type'} (op : type1400 B) : (term338 A B op) = (term335 A B op).
Proof. exact (MK_COMB (@lem5973897 A B) (@lem5973896 A B op)). Qed.
Lemma lem5973899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5973900 {A B : Type'} (op : type1400 B) : (term347 A B op) = (term348 A B op).
Proof. exact (MK_COMB (@lem5973899) (@lem5973898 A B op)). Qed.
Lemma lem5973901 {A B : Type'} (f : A -> B) (op : type1400 B) : (term342 A B op f) = (term327 A B f op).
Proof. exact (eq_refl (term342 A B op f)). Qed.
Lemma lem5973902 {A B : Type'} (op : type1400 B) : (term349 A B op) = (term340 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5973901 A B f op)). Qed.
Lemma lem5973903 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5973904 {A B : Type'} (op : type1400 B) : (term350 A B op) = (term351 A B op).
Proof. exact (MK_COMB (@lem5973903 A B) (@lem5973902 A B op)). Qed.
Lemma lem5973905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5973906 {A B : Type'} (op : type1400 B) : (term352 A B op) = (term353 A B op).
Proof. exact (MK_COMB (@lem5973905) (@lem5973904 A B op)). Qed.
Lemma lem5973907 {A B : Type'} (f : A -> B) (op : type1400 B) : (term344 A B op f) = (term332 A B f op).
Proof. exact (eq_refl (term344 A B op f)). Qed.
Lemma lem5973908 {A B : Type'} (op : type1400 B) : (term354 A B op) = (term341 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5973907 A B f op)). Qed.
Lemma lem5973909 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5973910 {A B : Type'} (op : type1400 B) : (term355 A B op) = (term356 A B op).
Proof. exact (MK_COMB (@lem5973909 A B) (@lem5973908 A B op)). Qed.
Lemma lem5973911 {A B : Type'} (op : type1400 B) : (term339 A B op) = (term357 A B op).
Proof. exact (MK_COMB (@lem5973906 A B op) (@lem5973910 A B op)). Qed.
Lemma lem5973912 {A B : Type'} (op : type1400 B) : ((term338 A B op) = (term339 A B op)) = ((term335 A B op) = (term357 A B op)).
Proof. exact (MK_COMB (@lem5973900 A B op) (@lem5973911 A B op)). Qed.
Lemma lem5973913 {A B : Type'} (op : type1400 B) : (term335 A B op) = (term357 A B op).
Proof. exact (EQ_MP (@lem5973912 A B op) (@lem5973890 A B op)). Qed.
Lemma lem5974026 {A B : Type'} (op : type1400 B) : (term285 A B op) = (term357 A B op).
Proof. exact (TRANS (@lem5973886 A B op) (@lem5973913 A B op)). Qed.
Lemma lem5974027 {A B : Type'} : (term286 A B) = (term358 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5974026 A B op)). Qed.
Lemma lem5974028 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5974029 {A B : Type'} : (term287 A B) = (term359 A B).
Proof. exact (MK_COMB (@lem5974028 B) (@lem5974027 A B)). Qed.
Lemma lem5974031 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term288 A P Q) = (term289 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5974032 {B : Type'} (P : type403 B) (Q : type403 B) : (term360 B P Q) = (term361 B P Q).
Proof. exact (@lem5974031 (type1400 B) P Q). Qed.
Lemma lem5974033 {A B : Type'} : (term362 A B) = (term363 A B).
Proof. exact (@lem5974032 B (term364 A B) (term365 A B)). Qed.
Lemma lem5974034 {A B : Type'} (op : type1400 B) : (term366 A B op) = (term351 A B op).
Proof. exact (eq_refl (term366 A B op)). Qed.
Lemma lem5974035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5974036 {A B : Type'} (op : type1400 B) : (term367 A B op) = (term353 A B op).
Proof. exact (MK_COMB (@lem5974035) (@lem5974034 A B op)). Qed.
Lemma lem5974037 {A B : Type'} (op : type1400 B) : (term368 A B op) = (term356 A B op).
Proof. exact (eq_refl (term368 A B op)). Qed.
Lemma lem5974038 {A B : Type'} (op : type1400 B) : (term369 A B op) = (term357 A B op).
Proof. exact (MK_COMB (@lem5974036 A B op) (@lem5974037 A B op)). Qed.
Lemma lem5974039 {A B : Type'} : (term370 A B) = (term358 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5974038 A B op)). Qed.
Lemma lem5974040 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5974041 {A B : Type'} : (term362 A B) = (term359 A B).
Proof. exact (MK_COMB (@lem5974040 B) (@lem5974039 A B)). Qed.
Lemma lem5974042 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5974043 {A B : Type'} : (term371 A B) = (term372 A B).
Proof. exact (MK_COMB (@lem5974042) (@lem5974041 A B)). Qed.
Lemma lem5974044 {A B : Type'} (op : type1400 B) : (term366 A B op) = (term351 A B op).
Proof. exact (eq_refl (term366 A B op)). Qed.
Lemma lem5974045 {A B : Type'} : (term373 A B) = (term364 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5974044 A B op)). Qed.
Lemma lem5974046 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5974047 {A B : Type'} : (term374 A B) = (term375 A B).
Proof. exact (MK_COMB (@lem5974046 B) (@lem5974045 A B)). Qed.
Lemma lem5974048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5974049 {A B : Type'} : (term376 A B) = (term377 A B).
Proof. exact (MK_COMB (@lem5974048) (@lem5974047 A B)). Qed.
Lemma lem5974050 {A B : Type'} (op : type1400 B) : (term368 A B op) = (term356 A B op).
Proof. exact (eq_refl (term368 A B op)). Qed.
Lemma lem5974051 {A B : Type'} : (term378 A B) = (term365 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5974050 A B op)). Qed.
Lemma lem5974052 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5974053 {A B : Type'} : (term379 A B) = (term380 A B).
Proof. exact (MK_COMB (@lem5974052 B) (@lem5974051 A B)). Qed.
Lemma lem5974054 {A B : Type'} : (term363 A B) = (term381 A B).
Proof. exact (MK_COMB (@lem5974049 A B) (@lem5974053 A B)). Qed.
Lemma lem5974055 {A B : Type'} : ((term362 A B) = (term363 A B)) = ((term359 A B) = (term381 A B)).
Proof. exact (MK_COMB (@lem5974043 A B) (@lem5974054 A B)). Qed.
Lemma lem5974056 {A B : Type'} : (term359 A B) = (term381 A B).
Proof. exact (EQ_MP (@lem5974055 A B) (@lem5974033 A B)). Qed.
Lemma lem5974179 {A B : Type'} : (term287 A B) = (term381 A B).
Proof. exact (TRANS (@lem5974029 A B) (@lem5974056 A B)). Qed.
Lemma lem5974180 {A B : Type'} : (term192 A B) = (term381 A B).
Proof. exact (TRANS (@lem5973613 A B) (@lem5974179 A B)). Qed.
Lemma lem5974181 {A B : Type'} (h1 : term192 A B) : term381 A B.
Proof. exact (EQ_MP (@lem5974180 A B) (@lem5972190 A B h1)). Qed.
Lemma lem5974182 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term268 A B op s f g x) : term268 A B op s f g x.
Proof. exact (h1). Qed.
Lemma lem5974192 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5974197 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974199 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5974197 A B f x). Qed.
Lemma lem5974204 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5974204 A B f x). Qed.
Lemma lem5974207 {A B : Type'} (g : A -> B) (x : A) : (g x) = (@I (A -> B) g x).
Proof. exact (@lem5974205 A B g x). Qed.
Lemma lem5974208 {A B : Type'} (f : A -> B) (x : A) : (term382 A B f x) = (term383 A B f x).
Proof. exact (MK_COMB (@lem5974192 B) (@lem5974199 A B f x)). Qed.
Lemma lem5974209 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : ((f x) = (g x)) = ((@I (A -> B) f x) = (@I (A -> B) g x)).
Proof. exact (MK_COMB (@lem5974208 A B f x) (@lem5974207 A B g x)). Qed.
Lemma lem5974210 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5974217 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974218 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5974217 A (type686 A) f x). Qed.
Lemma lem5974219 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5974218 A (@IN A) x). Qed.
Lemma lem5974220 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5974221 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5974219 A x) (@lem5974220 A s)). Qed.
Lemma lem5974223 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974224 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5974223 (A -> Prop) Prop f x). Qed.
Lemma lem5974225 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term384 A x s).
Proof. exact (@lem5974224 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5974227 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term384 A x s).
Proof. exact (TRANS (@lem5974221 A x s) (@lem5974225 A x s)). Qed.
Lemma lem5974228 {A : Type'} (x : A) (s : A -> Prop) : (term98 A x s) = (term385 A x s).
Proof. exact (MK_COMB (@lem5974210) (@lem5974227 A x s)). Qed.
Lemma lem5974229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5974230 {A : Type'} (x : A) (s : A -> Prop) : (term82 A x s) = (term386 A x s).
Proof. exact (MK_COMB (@lem5974229) (@lem5974228 A x s)). Qed.
Lemma lem5974231 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term78 A B s f g x) = (term387 A B s f g x).
Proof. exact (MK_COMB (@lem5974230 A x s) (@lem5974209 A B f g x)). Qed.
Lemma lem5974232 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term79 A B s f g) = (term388 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem5974231 A B s f g x)). Qed.
Lemma lem5974233 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5974234 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term80 A B s f g) = (term389 A B s f g).
Proof. exact (MK_COMB (@lem5974233 A) (@lem5974232 A B s f g)). Qed.
Lemma lem5974235 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term389 A B s f g.
Proof. exact (EQ_MP (@lem5974234 A B s f g) (@lem5972259 A B s f g h1)). Qed.
Lemma lem5974236 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem5974245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974246 {A B : Type'} (f : type748 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974245 (type1400 B) (type527 A B) f x). Qed.
Lemma lem5974247 {A B : Type'} (op : type1400 B) : (@support A B op) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op).
Proof. exact (@lem5974246 A B (@support A B) op). Qed.
Lemma lem5974248 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5974249 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f).
Proof. exact (MK_COMB (@lem5974247 A B op) (@lem5974248 A B f)). Qed.
Lemma lem5974251 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974252 {A B : Type'} (f : type527 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974251 (A -> B) (type672 A) f x). Qed.
Lemma lem5974253 {A B : Type'} (op : type1400 B) (f : A -> B) : (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f) = (term390 A B op f).
Proof. exact (@lem5974252 A B (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op) f). Qed.
Lemma lem5974254 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (term390 A B op f).
Proof. exact (TRANS (@lem5974249 A B op f) (@lem5974253 A B op f)). Qed.
Lemma lem5974255 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5974256 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term391 A B op f s).
Proof. exact (MK_COMB (@lem5974254 A B op f) (@lem5974255 A s)). Qed.
Lemma lem5974258 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974259 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974258 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5974260 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term391 A B op f s) = (term392 A B op f s).
Proof. exact (@lem5974259 A (term390 A B op f) s). Qed.
Lemma lem5974262 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term392 A B op f s).
Proof. exact (TRANS (@lem5974256 A B op f s) (@lem5974260 A B op f s)). Qed.
Lemma lem5974263 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term157 A B op f s) = (term393 A B op f s).
Proof. exact (MK_COMB (@lem5974236 A) (@lem5974262 A B op f s)). Qed.
Lemma lem5974265 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974266 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5974265 (A -> Prop) Prop f x). Qed.
Lemma lem5974267 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term393 A B op f s) = (term394 A B op f s).
Proof. exact (@lem5974266 A (@FINITE A) (term392 A B op f s)). Qed.
Lemma lem5974268 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term157 A B op f s) = (term394 A B op f s).
Proof. exact (TRANS (@lem5974263 A B op f s) (@lem5974267 A B op f s)). Qed.
Lemma lem5974670 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5974671 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5974676 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974678 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5974676 A B f x). Qed.
Lemma lem5974683 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974684 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5974683 (type1400 B) B f x). Qed.
Lemma lem5974686 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5974684 B (@neutral B) op). Qed.
Lemma lem5974687 {A B : Type'} (f : A -> B) (x : A) : (term382 A B f x) = (term383 A B f x).
Proof. exact (MK_COMB (@lem5974671 B) (@lem5974678 A B f x)). Qed.
Lemma lem5974688 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : ((f x) = (@neutral B op)) = ((@I (A -> B) f x) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem5974687 A B f x) (@lem5974686 B op)). Qed.
Lemma lem5974689 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term86 A B f x op) = (term395 A B f x op).
Proof. exact (MK_COMB (@lem5974670) (@lem5974688 A B f x op)). Qed.
Lemma lem5974696 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974697 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5974696 A (type686 A) f x). Qed.
Lemma lem5974698 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5974697 A (@IN A) x). Qed.
Lemma lem5974699 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5974700 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5974698 A x) (@lem5974699 A s)). Qed.
Lemma lem5974702 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974703 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5974702 (A -> Prop) Prop f x). Qed.
Lemma lem5974704 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term384 A x s).
Proof. exact (@lem5974703 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5974706 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term384 A x s).
Proof. exact (TRANS (@lem5974700 A x s) (@lem5974704 A x s)). Qed.
Lemma lem5974707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5974708 {A : Type'} (x : A) (s : A -> Prop) : (term396 A x s) = (term397 A x s).
Proof. exact (MK_COMB (@lem5974707) (@lem5974706 A x s)). Qed.
Lemma lem5974709 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term38 A B s f x op) = (term398 A B s f x op).
Proof. exact (MK_COMB (@lem5974708 A x s) (@lem5974689 A B f x op)). Qed.
Lemma lem5974710 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5974721 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974722 {A B : Type'} (f : type748 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974721 (type1400 B) (type527 A B) f x). Qed.
Lemma lem5974723 {A B : Type'} (op : type1400 B) : (@support A B op) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op).
Proof. exact (@lem5974722 A B (@support A B) op). Qed.
Lemma lem5974724 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5974725 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f).
Proof. exact (MK_COMB (@lem5974723 A B op) (@lem5974724 A B f)). Qed.
Lemma lem5974727 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974728 {A B : Type'} (f : type527 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974727 (A -> B) (type672 A) f x). Qed.
Lemma lem5974729 {A B : Type'} (op : type1400 B) (f : A -> B) : (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f) = (term390 A B op f).
Proof. exact (@lem5974728 A B (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op) f). Qed.
Lemma lem5974730 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (term390 A B op f).
Proof. exact (TRANS (@lem5974725 A B op f) (@lem5974729 A B op f)). Qed.
Lemma lem5974731 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5974732 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term391 A B op f s).
Proof. exact (MK_COMB (@lem5974730 A B op f) (@lem5974731 A s)). Qed.
Lemma lem5974734 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974735 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974734 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5974736 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term391 A B op f s) = (term392 A B op f s).
Proof. exact (@lem5974735 A (term390 A B op f) s). Qed.
Lemma lem5974738 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term392 A B op f s).
Proof. exact (TRANS (@lem5974732 A B op f s) (@lem5974736 A B op f s)). Qed.
Lemma lem5974739 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5974740 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term37 A B x op f s) = (term399 A B x op f s).
Proof. exact (MK_COMB (@lem5974739 A x) (@lem5974738 A B op f s)). Qed.
Lemma lem5974742 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974743 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5974742 A (type686 A) f x). Qed.
Lemma lem5974744 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5974743 A (@IN A) x). Qed.
Lemma lem5974745 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term392 A B op f s) = (term392 A B op f s).
Proof. exact (eq_refl (term392 A B op f s)). Qed.
Lemma lem5974746 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term399 A B x op f s) = (term400 A B x op f s).
Proof. exact (MK_COMB (@lem5974744 A x) (@lem5974745 A B op f s)). Qed.
Lemma lem5974748 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974749 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5974748 (A -> Prop) Prop f x). Qed.
Lemma lem5974750 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term400 A B x op f s) = (term401 A B x op f s).
Proof. exact (@lem5974749 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) (term392 A B op f s)). Qed.
Lemma lem5974751 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term399 A B x op f s) = (term401 A B x op f s).
Proof. exact (TRANS (@lem5974746 A B x op f s) (@lem5974750 A B x op f s)). Qed.
Lemma lem5974752 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term37 A B x op f s) = (term401 A B x op f s).
Proof. exact (TRANS (@lem5974740 A B x op f s) (@lem5974751 A B x op f s)). Qed.
Lemma lem5974753 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term402 A B x op f s) = (term403 A B x op f s).
Proof. exact (MK_COMB (@lem5974710) (@lem5974752 A B x op f s)). Qed.
Lemma lem5974754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5974755 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term404 A B x op f s) = (term405 A B x op f s).
Proof. exact (MK_COMB (@lem5974754) (@lem5974753 A B x op f s)). Qed.
Lemma lem5974756 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term272 A B s f x op) = (term406 A B s f x op).
Proof. exact (MK_COMB (@lem5974755 A B x op f s) (@lem5974709 A B s f x op)). Qed.
Lemma lem5974757 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term295 A B f x op) = (term407 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5974756 A B s f x op)). Qed.
Lemma lem5974758 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5974759 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term310 A B f x op) = (term408 A B f x op).
Proof. exact (MK_COMB (@lem5974758 A) (@lem5974757 A B f x op)). Qed.
Lemma lem5974760 {A B : Type'} (f : A -> B) (op : type1400 B) : (term317 A B f op) = (term409 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5974759 A B f x op)). Qed.
Lemma lem5974761 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5974762 {A B : Type'} (f : A -> B) (op : type1400 B) : (term332 A B f op) = (term410 A B f op).
Proof. exact (MK_COMB (@lem5974761 A) (@lem5974760 A B f op)). Qed.
Lemma lem5974763 {A B : Type'} (op : type1400 B) : (term341 A B op) = (term411 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5974762 A B f op)). Qed.
Lemma lem5974764 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5974765 {A B : Type'} (op : type1400 B) : (term356 A B op) = (term412 A B op).
Proof. exact (MK_COMB (@lem5974764 A B) (@lem5974763 A B op)). Qed.
Lemma lem5974766 {A B : Type'} : (term365 A B) = (term413 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5974765 A B op)). Qed.
Lemma lem5974767 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5974768 {A B : Type'} : (term380 A B) = (term414 A B).
Proof. exact (MK_COMB (@lem5974767 B) (@lem5974766 A B)). Qed.
Lemma lem5974769 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5974774 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974776 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5974774 A B f x). Qed.
Lemma lem5974781 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974782 {B : Type'} (f : type402 B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> B) f x).
Proof. exact (@lem5974781 (type1400 B) B f x). Qed.
Lemma lem5974784 {B : Type'} (op : type1400 B) : (@neutral B op) = (@I ((B -> B -> B) -> B) (@neutral B) op).
Proof. exact (@lem5974782 B (@neutral B) op). Qed.
Lemma lem5974785 {A B : Type'} (f : A -> B) (x : A) : (term382 A B f x) = (term383 A B f x).
Proof. exact (MK_COMB (@lem5974769 B) (@lem5974776 A B f x)). Qed.
Lemma lem5974786 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : ((f x) = (@neutral B op)) = ((@I (A -> B) f x) = (@I ((B -> B -> B) -> B) (@neutral B) op)).
Proof. exact (MK_COMB (@lem5974785 A B f x) (@lem5974784 B op)). Qed.
Lemma lem5974787 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5974794 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974795 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5974794 A (type686 A) f x). Qed.
Lemma lem5974796 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5974795 A (@IN A) x). Qed.
Lemma lem5974797 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5974798 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5974796 A x) (@lem5974797 A s)). Qed.
Lemma lem5974800 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974801 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5974800 (A -> Prop) Prop f x). Qed.
Lemma lem5974802 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term384 A x s).
Proof. exact (@lem5974801 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5974804 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term384 A x s).
Proof. exact (TRANS (@lem5974798 A x s) (@lem5974802 A x s)). Qed.
Lemma lem5974805 {A : Type'} (x : A) (s : A -> Prop) : (term98 A x s) = (term385 A x s).
Proof. exact (MK_COMB (@lem5974787) (@lem5974804 A x s)). Qed.
Lemma lem5974806 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5974807 {A : Type'} (x : A) (s : A -> Prop) : (term82 A x s) = (term386 A x s).
Proof. exact (MK_COMB (@lem5974806) (@lem5974805 A x s)). Qed.
Lemma lem5974808 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term84 A B s f x op) = (term415 A B s f x op).
Proof. exact (MK_COMB (@lem5974807 A x s) (@lem5974786 A B f x op)). Qed.
Lemma lem5974819 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974820 {A B : Type'} (f : type748 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974819 (type1400 B) (type527 A B) f x). Qed.
Lemma lem5974821 {A B : Type'} (op : type1400 B) : (@support A B op) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op).
Proof. exact (@lem5974820 A B (@support A B) op). Qed.
Lemma lem5974822 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5974823 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f).
Proof. exact (MK_COMB (@lem5974821 A B op) (@lem5974822 A B f)). Qed.
Lemma lem5974825 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974826 {A B : Type'} (f : type527 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974825 (A -> B) (type672 A) f x). Qed.
Lemma lem5974827 {A B : Type'} (op : type1400 B) (f : A -> B) : (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f) = (term390 A B op f).
Proof. exact (@lem5974826 A B (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op) f). Qed.
Lemma lem5974828 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (term390 A B op f).
Proof. exact (TRANS (@lem5974823 A B op f) (@lem5974827 A B op f)). Qed.
Lemma lem5974829 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5974830 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term391 A B op f s).
Proof. exact (MK_COMB (@lem5974828 A B op f) (@lem5974829 A s)). Qed.
Lemma lem5974832 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974833 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974832 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5974834 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term391 A B op f s) = (term392 A B op f s).
Proof. exact (@lem5974833 A (term390 A B op f) s). Qed.
Lemma lem5974836 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term392 A B op f s).
Proof. exact (TRANS (@lem5974830 A B op f s) (@lem5974834 A B op f s)). Qed.
Lemma lem5974837 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5974838 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term37 A B x op f s) = (term399 A B x op f s).
Proof. exact (MK_COMB (@lem5974837 A x) (@lem5974836 A B op f s)). Qed.
Lemma lem5974840 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974841 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5974840 A (type686 A) f x). Qed.
Lemma lem5974842 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5974841 A (@IN A) x). Qed.
Lemma lem5974843 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term392 A B op f s) = (term392 A B op f s).
Proof. exact (eq_refl (term392 A B op f s)). Qed.
Lemma lem5974844 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term399 A B x op f s) = (term400 A B x op f s).
Proof. exact (MK_COMB (@lem5974842 A x) (@lem5974843 A B op f s)). Qed.
Lemma lem5974846 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974847 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5974846 (A -> Prop) Prop f x). Qed.
Lemma lem5974848 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term400 A B x op f s) = (term401 A B x op f s).
Proof. exact (@lem5974847 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) (term392 A B op f s)). Qed.
Lemma lem5974849 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term399 A B x op f s) = (term401 A B x op f s).
Proof. exact (TRANS (@lem5974844 A B x op f s) (@lem5974848 A B x op f s)). Qed.
Lemma lem5974850 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term37 A B x op f s) = (term401 A B x op f s).
Proof. exact (TRANS (@lem5974838 A B x op f s) (@lem5974849 A B x op f s)). Qed.
Lemma lem5974851 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5974852 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term273 A B x op f s) = (term416 A B x op f s).
Proof. exact (MK_COMB (@lem5974851) (@lem5974850 A B x op f s)). Qed.
Lemma lem5974853 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term275 A B s f x op) = (term417 A B s f x op).
Proof. exact (MK_COMB (@lem5974852 A B x op f s) (@lem5974808 A B s f x op)). Qed.
Lemma lem5974854 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term294 A B f x op) = (term418 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5974853 A B s f x op)). Qed.
Lemma lem5974855 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5974856 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term305 A B f x op) = (term419 A B f x op).
Proof. exact (MK_COMB (@lem5974855 A) (@lem5974854 A B f x op)). Qed.
Lemma lem5974857 {A B : Type'} (f : A -> B) (op : type1400 B) : (term316 A B f op) = (term420 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5974856 A B f x op)). Qed.
Lemma lem5974858 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5974859 {A B : Type'} (f : A -> B) (op : type1400 B) : (term327 A B f op) = (term421 A B f op).
Proof. exact (MK_COMB (@lem5974858 A) (@lem5974857 A B f op)). Qed.
Lemma lem5974860 {A B : Type'} (op : type1400 B) : (term340 A B op) = (term422 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5974859 A B f op)). Qed.
Lemma lem5974861 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5974862 {A B : Type'} (op : type1400 B) : (term351 A B op) = (term423 A B op).
Proof. exact (MK_COMB (@lem5974861 A B) (@lem5974860 A B op)). Qed.
Lemma lem5974863 {A B : Type'} : (term364 A B) = (term424 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5974862 A B op)). Qed.
Lemma lem5974864 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5974865 {A B : Type'} : (term375 A B) = (term425 A B).
Proof. exact (MK_COMB (@lem5974864 B) (@lem5974863 A B)). Qed.
Lemma lem5974866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5974867 {A B : Type'} : (term377 A B) = (term426 A B).
Proof. exact (MK_COMB (@lem5974866) (@lem5974865 A B)). Qed.
Lemma lem5974868 {A B : Type'} : (term381 A B) = (term427 A B).
Proof. exact (MK_COMB (@lem5974867 A B) (@lem5974768 A B)). Qed.
Lemma lem5974869 {A B : Type'} (h1 : term192 A B) : term427 A B.
Proof. exact (EQ_MP (@lem5974868 A B) (@lem5974181 A B h1)). Qed.
Lemma lem5974870 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5974871 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5974876 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974878 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5974876 A B f x). Qed.
Lemma lem5974883 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974884 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5974883 A B f x). Qed.
Lemma lem5974886 {A B : Type'} (g : A -> B) (x : A) : (g x) = (@I (A -> B) g x).
Proof. exact (@lem5974884 A B g x). Qed.
Lemma lem5974887 {A B : Type'} (f : A -> B) (x : A) : (term382 A B f x) = (term383 A B f x).
Proof. exact (MK_COMB (@lem5974871 B) (@lem5974878 A B f x)). Qed.
Lemma lem5974888 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : ((f x) = (g x)) = ((@I (A -> B) f x) = (@I (A -> B) g x)).
Proof. exact (MK_COMB (@lem5974887 A B f x) (@lem5974886 A B g x)). Qed.
Lemma lem5974889 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term114 A B f g x) = (term428 A B f g x).
Proof. exact (MK_COMB (@lem5974870) (@lem5974888 A B f g x)). Qed.
Lemma lem5974900 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974901 {A B : Type'} (f : type748 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974900 (type1400 B) (type527 A B) f x). Qed.
Lemma lem5974902 {A B : Type'} (op : type1400 B) : (@support A B op) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op).
Proof. exact (@lem5974901 A B (@support A B) op). Qed.
Lemma lem5974903 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5974904 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f).
Proof. exact (MK_COMB (@lem5974902 A B op) (@lem5974903 A B f)). Qed.
Lemma lem5974906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974907 {A B : Type'} (f : type527 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974906 (A -> B) (type672 A) f x). Qed.
Lemma lem5974908 {A B : Type'} (op : type1400 B) (f : A -> B) : (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f) = (term390 A B op f).
Proof. exact (@lem5974907 A B (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op) f). Qed.
Lemma lem5974909 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (term390 A B op f).
Proof. exact (TRANS (@lem5974904 A B op f) (@lem5974908 A B op f)). Qed.
Lemma lem5974910 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5974911 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term391 A B op f s).
Proof. exact (MK_COMB (@lem5974909 A B op f) (@lem5974910 A s)). Qed.
Lemma lem5974913 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974914 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974913 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5974915 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term391 A B op f s) = (term392 A B op f s).
Proof. exact (@lem5974914 A (term390 A B op f) s). Qed.
Lemma lem5974917 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term392 A B op f s).
Proof. exact (TRANS (@lem5974911 A B op f s) (@lem5974915 A B op f s)). Qed.
Lemma lem5974918 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem5974919 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term37 A B x op f s) = (term399 A B x op f s).
Proof. exact (MK_COMB (@lem5974918 A x) (@lem5974917 A B op f s)). Qed.
Lemma lem5974921 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974922 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5974921 A (type686 A) f x). Qed.
Lemma lem5974923 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5974922 A (@IN A) x). Qed.
Lemma lem5974924 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term392 A B op f s) = (term392 A B op f s).
Proof. exact (eq_refl (term392 A B op f s)). Qed.
Lemma lem5974925 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term399 A B x op f s) = (term400 A B x op f s).
Proof. exact (MK_COMB (@lem5974923 A x) (@lem5974924 A B op f s)). Qed.
Lemma lem5974927 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974928 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5974927 (A -> Prop) Prop f x). Qed.
Lemma lem5974929 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term400 A B x op f s) = (term401 A B x op f s).
Proof. exact (@lem5974928 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) (term392 A B op f s)). Qed.
Lemma lem5974930 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term399 A B x op f s) = (term401 A B x op f s).
Proof. exact (TRANS (@lem5974925 A B x op f s) (@lem5974929 A B x op f s)). Qed.
Lemma lem5974931 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term37 A B x op f s) = (term401 A B x op f s).
Proof. exact (TRANS (@lem5974919 A B x op f s) (@lem5974930 A B x op f s)). Qed.
Lemma lem5974932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5974933 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term429 A B x op f s) = (term430 A B x op f s).
Proof. exact (MK_COMB (@lem5974932) (@lem5974931 A B x op f s)). Qed.
Lemma lem5974934 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term245 A B op s f g x) = (term431 A B op s f g x).
Proof. exact (MK_COMB (@lem5974933 A B x op f s) (@lem5974889 A B f g x)). Qed.
Lemma lem5974935 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5974936 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem5974945 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974946 {A B : Type'} (f : type748 A B) (x : type1400 B) : (f x) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974945 (type1400 B) (type527 A B) f x). Qed.
Lemma lem5974947 {A B : Type'} (op : type1400 B) : (@support A B op) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op).
Proof. exact (@lem5974946 A B (@support A B) op). Qed.
Lemma lem5974948 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5974949 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f).
Proof. exact (MK_COMB (@lem5974947 A B op) (@lem5974948 A B f)). Qed.
Lemma lem5974951 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974952 {A B : Type'} (f : type527 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974951 (A -> B) (type672 A) f x). Qed.
Lemma lem5974953 {A B : Type'} (op : type1400 B) (f : A -> B) : (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op f) = (term390 A B op f).
Proof. exact (@lem5974952 A B (@I ((B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop) (@support A B) op) f). Qed.
Lemma lem5974954 {A B : Type'} (op : type1400 B) (f : A -> B) : (@support A B op f) = (term390 A B op f).
Proof. exact (TRANS (@lem5974949 A B op f) (@lem5974953 A B op f)). Qed.
Lemma lem5974955 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5974956 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term391 A B op f s).
Proof. exact (MK_COMB (@lem5974954 A B op f) (@lem5974955 A s)). Qed.
Lemma lem5974958 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974959 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5974958 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5974960 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term391 A B op f s) = (term392 A B op f s).
Proof. exact (@lem5974959 A (term390 A B op f) s). Qed.
Lemma lem5974962 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (@support A B op f s) = (term392 A B op f s).
Proof. exact (TRANS (@lem5974956 A B op f s) (@lem5974960 A B op f s)). Qed.
Lemma lem5974963 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term157 A B op f s) = (term393 A B op f s).
Proof. exact (MK_COMB (@lem5974936 A) (@lem5974962 A B op f s)). Qed.
Lemma lem5974965 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5974966 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5974965 (A -> Prop) Prop f x). Qed.
Lemma lem5974967 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term393 A B op f s) = (term394 A B op f s).
Proof. exact (@lem5974966 A (@FINITE A) (term392 A B op f s)). Qed.
Lemma lem5974968 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term157 A B op f s) = (term394 A B op f s).
Proof. exact (TRANS (@lem5974963 A B op f s) (@lem5974967 A B op f s)). Qed.
Lemma lem5974969 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term177 A B op f s) = (term432 A B op f s).
Proof. exact (MK_COMB (@lem5974935) (@lem5974968 A B op f s)). Qed.
Lemma lem5974970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5974971 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term255 A B op f s) = (term433 A B op f s).
Proof. exact (MK_COMB (@lem5974970) (@lem5974969 A B op f s)). Qed.
Lemma lem5974972 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term268 A B op s f g x) = (term434 A B op s f g x).
Proof. exact (MK_COMB (@lem5974971 A B op f s) (@lem5974934 A B op s f g x)). Qed.
Lemma lem5974973 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term268 A B op s f g x) : term434 A B op s f g x.
Proof. exact (EQ_MP (@lem5974972 A B op s f g x) (@lem5974182 A B op s f g x h1)). Qed.
Lemma lem5974974 {A B : Type'} (h1 : term192 A B) : term414 A B.
Proof. exact (proj2 (@lem5974869 A B h1)). Qed.
Lemma lem5974981 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term431 A B op s f g x) : term431 A B op s f g x.
Proof. exact (h1). Qed.
Lemma lem5975188 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term432 A B op f s) : term432 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5975200 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term387 A B s f g x) = (term387 A B s f g x).
Proof. exact (eq_refl (term387 A B s f g x)). Qed.
Lemma lem5975201 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term388 A B s f g) = (term388 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem5975200 A B s f g x)). Qed.
Lemma lem5975202 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5975204 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term389 A B s f g) = (term389 A B s f g).
Proof. exact (MK_COMB (@lem5975202 A) (@lem5975201 A B s f g)). Qed.
Lemma lem5975205 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term389 A B s f g.
Proof. exact (EQ_MP (@lem5975204 A B s f g) (@lem5974235 A B s f g h1)). Qed.
Lemma lem5975255 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (op : type1400 B) : (term406 A B s f x op) = (term435 A B s f x op).
Proof. exact (@lem19490 (term384 A x s) (term403 A B x op f s) (term395 A B f x op)). Qed.
Lemma lem5975256 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term407 A B f x op) = (term436 A B f x op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5975255 A B s f x op)). Qed.
Lemma lem5975257 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5975258 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) : (term408 A B f x op) = (term437 A B f x op).
Proof. exact (MK_COMB (@lem5975257 A) (@lem5975256 A B f x op)). Qed.
Lemma lem5975259 {A B : Type'} (f : A -> B) (op : type1400 B) : (term409 A B f op) = (term438 A B f op).
Proof. exact (fun_ext (fun x : A => @lem5975258 A B f x op)). Qed.
Lemma lem5975260 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5975261 {A B : Type'} (f : A -> B) (op : type1400 B) : (term410 A B f op) = (term439 A B f op).
Proof. exact (MK_COMB (@lem5975260 A) (@lem5975259 A B f op)). Qed.
Lemma lem5975262 {A B : Type'} (op : type1400 B) : (term411 A B op) = (term440 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5975261 A B f op)). Qed.
Lemma lem5975263 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5975264 {A B : Type'} (op : type1400 B) : (term412 A B op) = (term441 A B op).
Proof. exact (MK_COMB (@lem5975263 A B) (@lem5975262 A B op)). Qed.
Lemma lem5975265 {A B : Type'} : (term413 A B) = (term442 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5975264 A B op)). Qed.
Lemma lem5975266 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5975268 {A B : Type'} : (term414 A B) = (term443 A B).
Proof. exact (MK_COMB (@lem5975266 B) (@lem5975265 A B)). Qed.
Lemma lem5975269 {A B : Type'} (h1 : term192 A B) : term443 A B.
Proof. exact (EQ_MP (@lem5975268 A B) (@lem5974974 A B h1)). Qed.
Lemma lem5975473 {A B : Type'} (_75757 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term444 A B s f g _75757.
Proof. exact (@lem5975205 A B s f g h1 _75757). Qed.
Lemma lem5975474 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_75757 : A) : (term444 A B s f g _75757) = (term387 A B s f g _75757).
Proof. exact (eq_refl (term444 A B s f g _75757)). Qed.
Lemma lem5975488 {A B : Type'} (_75762 : type1400 B) (h1 : term192 A B) : term445 A B _75762.
Proof. exact (@lem5975269 A B h1 _75762). Qed.
Lemma lem5975489 {A B : Type'} (_75762 : type1400 B) : (term445 A B _75762) = (term441 A B _75762).
Proof. exact (eq_refl (term445 A B _75762)). Qed.
Lemma lem5975490 {A B : Type'} (_75762 : type1400 B) (h1 : term192 A B) : term441 A B _75762.
Proof. exact (EQ_MP (@lem5975489 A B _75762) (@lem5975488 A B _75762 h1)). Qed.
Lemma lem5975491 {A B : Type'} (_75762 : type1400 B) (_75763 : A -> B) (h1 : term192 A B) : term446 A B _75762 _75763.
Proof. exact (@lem5975490 A B _75762 h1 _75763). Qed.
Lemma lem5975492 {A B : Type'} (_75763 : A -> B) (_75762 : type1400 B) : (term446 A B _75762 _75763) = (term439 A B _75763 _75762).
Proof. exact (eq_refl (term446 A B _75762 _75763)). Qed.
Lemma lem5975493 {A B : Type'} (_75763 : A -> B) (_75762 : type1400 B) (h1 : term192 A B) : term439 A B _75763 _75762.
Proof. exact (EQ_MP (@lem5975492 A B _75763 _75762) (@lem5975491 A B _75762 _75763 h1)). Qed.
Lemma lem5975494 {A B : Type'} (_75763 : A -> B) (_75762 : type1400 B) (_75764 : A) (h1 : term192 A B) : term447 A B _75763 _75762 _75764.
Proof. exact (@lem5975493 A B _75763 _75762 h1 _75764). Qed.
Lemma lem5975495 {A B : Type'} (_75763 : A -> B) (_75764 : A) (_75762 : type1400 B) : (term447 A B _75763 _75762 _75764) = (term437 A B _75763 _75764 _75762).
Proof. exact (eq_refl (term447 A B _75763 _75762 _75764)). Qed.
Lemma lem5975496 {A B : Type'} (_75763 : A -> B) (_75764 : A) (_75762 : type1400 B) (h1 : term192 A B) : term437 A B _75763 _75764 _75762.
Proof. exact (EQ_MP (@lem5975495 A B _75763 _75764 _75762) (@lem5975494 A B _75763 _75762 _75764 h1)). Qed.
Lemma lem5975497 {A B : Type'} (_75763 : A -> B) (_75764 : A) (_75762 : type1400 B) (_75765 : A -> Prop) (h1 : term192 A B) : term448 A B _75763 _75764 _75762 _75765.
Proof. exact (@lem5975496 A B _75763 _75764 _75762 h1 _75765). Qed.
Lemma lem5975498 {A B : Type'} (_75765 : A -> Prop) (_75763 : A -> B) (_75764 : A) (_75762 : type1400 B) : (term448 A B _75763 _75764 _75762 _75765) = (term435 A B _75765 _75763 _75764 _75762).
Proof. exact (eq_refl (term448 A B _75763 _75764 _75762 _75765)). Qed.
Lemma lem5975499 {A B : Type'} (_75765 : A -> Prop) (_75763 : A -> B) (_75764 : A) (_75762 : type1400 B) (h1 : term192 A B) : term435 A B _75765 _75763 _75764 _75762.
Proof. exact (EQ_MP (@lem5975498 A B _75765 _75763 _75764 _75762) (@lem5975497 A B _75763 _75764 _75762 _75765 h1)). Qed.
Lemma lem5975601 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term432 A B op f s) : term432 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5975645 {A B : Type'} (_75757 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term387 A B s f g _75757.
Proof. exact (EQ_MP (@lem5975474 A B s f g _75757) (@lem5975473 A B _75757 s f g h1)). Qed.
Lemma lem5975681 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term431 A B op s f g x) : term428 A B f g x.
Proof. exact (proj2 (@lem5974981 A B op s f g x h1)). Qed.
Lemma lem5975711 {A B : Type'} (_75762 : type1400 B) (_75763 : A -> B) (_75764 : A) (_75765 : A -> Prop) (h1 : term192 A B) : term449 A B _75762 _75763 _75764 _75765.
Proof. exact (proj1 (@lem5975499 A B _75765 _75763 _75764 _75762 h1)). Qed.
Lemma lem5976053 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) : term394 A B op f s.
Proof. exact (EQ_MP (@lem5974268 A B op f s) (@lem5972265 A B op f s h1)). Qed.
Lemma lem5976054 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) : term450 A B op f s.
Proof. exact (fun h0 : term432 A B op f s => @lem5976053 A B op f s h1). Qed.
Lemma lem5976056 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5976057 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term450 A B op f s) = (term394 A B op f s).
Proof. exact (@lem5976056 (term394 A B op f s)). Qed.
Lemma lem5976058 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) : term394 A B op f s.
Proof. exact (EQ_MP (@lem5976057 A B op f s) (@lem5976054 A B op f s h1)). Qed.
Lemma lem5976061 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5976063 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term432 A B op f s) = (term451 A B op f s).
Proof. exact (@lem5976061 (term394 A B op f s)). Qed.
Lemma lem5976066 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term432 A B op f s) : term451 A B op f s.
Proof. exact (EQ_MP (@lem5976063 A B op f s) (@lem5975601 A B op f s h1)). Qed.
Lemma lem5976069 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) (h2 : term432 A B op f s) : False.
Proof. exact (@lem5976066 A B op f s h2 (@lem5976058 A B op f s h1)). Qed.
Lemma lem5976070 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) (h2 : term432 A B op f s) : term103.
Proof. exact (fun h0 : ~ False => @lem5976069 A B op f s h1 h2). Qed.
Lemma lem5976072 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5976073 : term103 = False.
Proof. exact (@lem5976072 False). Qed.
Lemma lem5976074 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) (h2 : term432 A B op f s) : False.
Proof. exact (EQ_MP (@lem5976073) (@lem5976070 A B op f s h1 h2)). Qed.
Lemma lem5976410 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term431 A B op s f g x) : term401 A B x op f s.
Proof. exact (proj1 (@lem5974981 A B op s f g x h1)). Qed.
Lemma lem5976411 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term431 A B op s f g x) : term452 A B x op f s.
Proof. exact (fun h0 : term403 A B x op f s => @lem5976410 A B op s f g x h1). Qed.
Lemma lem5976413 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5976414 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term452 A B x op f s) = (term401 A B x op f s).
Proof. exact (@lem5976413 (term401 A B x op f s)). Qed.
Lemma lem5976415 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term431 A B op s f g x) : term401 A B x op f s.
Proof. exact (EQ_MP (@lem5976414 A B x op f s) (@lem5976411 A B op s f g x h1)). Qed.
Lemma lem5976421 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5976422 {A B : Type'} (_75764 : A) (_75762 : type1400 B) (_75763 : A -> B) (_75765 : A -> Prop) : (term449 A B _75762 _75763 _75764 _75765) = (term453 A B _75764 _75762 _75763 _75765).
Proof. exact (@lem5976421 (term384 A _75764 _75765) (term403 A B _75764 _75762 _75763 _75765)). Qed.
Lemma lem5976428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5976429 {A B : Type'} (_75764 : A) (_75762 : type1400 B) (_75763 : A -> B) (_75765 : A -> Prop) : (term454 A B _75762 _75763 _75764 _75765) = (term455 A B _75764 _75762 _75763 _75765).
Proof. exact (MK_COMB (@lem5976428) (@lem5976422 A B _75764 _75762 _75763 _75765)). Qed.
Lemma lem5976435 {A B : Type'} (_75764 : A) (_75762 : type1400 B) (_75763 : A -> B) (_75765 : A -> Prop) : (term453 A B _75764 _75762 _75763 _75765) = (term453 A B _75764 _75762 _75763 _75765).
Proof. exact (eq_refl (term453 A B _75764 _75762 _75763 _75765)). Qed.
Lemma lem5976436 {A B : Type'} (_75764 : A) (_75762 : type1400 B) (_75763 : A -> B) (_75765 : A -> Prop) : ((term449 A B _75762 _75763 _75764 _75765) = (term453 A B _75764 _75762 _75763 _75765)) = ((term453 A B _75764 _75762 _75763 _75765) = (term453 A B _75764 _75762 _75763 _75765)).
Proof. exact (MK_COMB (@lem5976429 A B _75764 _75762 _75763 _75765) (@lem5976435 A B _75764 _75762 _75763 _75765)). Qed.
Lemma lem5976438 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5976439 (x : Prop) : (x = x) = True.
Proof. exact (@lem5976438 Prop x). Qed.
Lemma lem5976440 {A B : Type'} (_75764 : A) (_75762 : type1400 B) (_75763 : A -> B) (_75765 : A -> Prop) : ((term453 A B _75764 _75762 _75763 _75765) = (term453 A B _75764 _75762 _75763 _75765)) = True.
Proof. exact (@lem5976439 (term453 A B _75764 _75762 _75763 _75765)). Qed.
Lemma lem5976441 {A B : Type'} (_75764 : A) (_75762 : type1400 B) (_75763 : A -> B) (_75765 : A -> Prop) : ((term449 A B _75762 _75763 _75764 _75765) = (term453 A B _75764 _75762 _75763 _75765)) = True.
Proof. exact (TRANS (@lem5976436 A B _75764 _75762 _75763 _75765) (@lem5976440 A B _75764 _75762 _75763 _75765)). Qed.
Lemma lem5976442 {A B : Type'} (_75764 : A) (_75762 : type1400 B) (_75763 : A -> B) (_75765 : A -> Prop) : True = ((term449 A B _75762 _75763 _75764 _75765) = (term453 A B _75764 _75762 _75763 _75765)).
Proof. exact (SYM (@lem5976441 A B _75764 _75762 _75763 _75765)). Qed.
Lemma lem5976443 {A B : Type'} (_75764 : A) (_75762 : type1400 B) (_75763 : A -> B) (_75765 : A -> Prop) : (term449 A B _75762 _75763 _75764 _75765) = (term453 A B _75764 _75762 _75763 _75765).
Proof. exact (EQ_MP (@lem5976442 A B _75764 _75762 _75763 _75765) (@lem0)). Qed.
Lemma lem5976444 {A B : Type'} (_75764 : A) (_75762 : type1400 B) (_75763 : A -> B) (_75765 : A -> Prop) (h1 : term192 A B) : term453 A B _75764 _75762 _75763 _75765.
Proof. exact (EQ_MP (@lem5976443 A B _75764 _75762 _75763 _75765) (@lem5975711 A B _75762 _75763 _75764 _75765 h1)). Qed.
Lemma lem5976446 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5976447 {A B : Type'} (_75762 : type1400 B) (_75763 : A -> B) (_75764 : A) (_75765 : A -> Prop) : (term453 A B _75764 _75762 _75763 _75765) = (term456 A B _75762 _75763 _75764 _75765).
Proof. exact (@lem5976446 (term403 A B _75764 _75762 _75763 _75765) (term384 A _75764 _75765)). Qed.
Lemma lem5976449 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5976450 {A B : Type'} (_75764 : A) (_75762 : type1400 B) (_75763 : A -> B) (_75765 : A -> Prop) : (term457 A B _75764 _75762 _75763 _75765) = (term401 A B _75764 _75762 _75763 _75765).
Proof. exact (@lem5976449 (term401 A B _75764 _75762 _75763 _75765)). Qed.
Lemma lem5976451 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5976452 {A B : Type'} (_75764 : A) (_75762 : type1400 B) (_75763 : A -> B) (_75765 : A -> Prop) : (term458 A B _75764 _75762 _75763 _75765) = (term459 A B _75764 _75762 _75763 _75765).
Proof. exact (MK_COMB (@lem5976451) (@lem5976450 A B _75764 _75762 _75763 _75765)). Qed.
Lemma lem5976453 {A : Type'} (_75764 : A) (_75765 : A -> Prop) : (term384 A _75764 _75765) = (term384 A _75764 _75765).
Proof. exact (eq_refl (term384 A _75764 _75765)). Qed.
Lemma lem5976454 {A B : Type'} (_75762 : type1400 B) (_75763 : A -> B) (_75764 : A) (_75765 : A -> Prop) : (term456 A B _75762 _75763 _75764 _75765) = (term460 A B _75762 _75763 _75764 _75765).
Proof. exact (MK_COMB (@lem5976452 A B _75764 _75762 _75763 _75765) (@lem5976453 A _75764 _75765)). Qed.
Lemma lem5976455 {A B : Type'} (_75762 : type1400 B) (_75763 : A -> B) (_75764 : A) (_75765 : A -> Prop) : (term453 A B _75764 _75762 _75763 _75765) = (term460 A B _75762 _75763 _75764 _75765).
Proof. exact (TRANS (@lem5976447 A B _75762 _75763 _75764 _75765) (@lem5976454 A B _75762 _75763 _75764 _75765)). Qed.
Lemma lem5976458 {A B : Type'} (_75762 : type1400 B) (_75763 : A -> B) (_75764 : A) (_75765 : A -> Prop) (h1 : term192 A B) : term460 A B _75762 _75763 _75764 _75765.
Proof. exact (EQ_MP (@lem5976455 A B _75762 _75763 _75764 _75765) (@lem5976444 A B _75764 _75762 _75763 _75765 h1)). Qed.
Lemma lem5976459 {A B : Type'} (_75762 : type1400 B) (_75763 : A -> B) (_75764 : A) (_75765 : A -> Prop) (h1 : term192 A B) : term460 A B _75762 _75763 _75764 _75765.
Proof. exact (@lem5976458 A B _75762 _75763 _75764 _75765 h1). Qed.
Lemma lem5976460 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term192 A B) : term460 A B op f x s.
Proof. exact (@lem5976459 A B op f x s h1). Qed.
Lemma lem5976463 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term192 A B) (h2 : term431 A B op s f g x) : term384 A x s.
Proof. exact (@lem5976460 A B op f x s h1 (@lem5976415 A B op s f g x h2)). Qed.
Lemma lem5976464 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term192 A B) (h2 : term431 A B op s f g x) : term461 A x s.
Proof. exact (fun h0 : term385 A x s => @lem5976463 A B op s f g x h1 h2). Qed.
Lemma lem5976466 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5976467 {A : Type'} (x : A) (s : A -> Prop) : (term461 A x s) = (term384 A x s).
Proof. exact (@lem5976466 (term384 A x s)). Qed.
Lemma lem5976468 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term192 A B) (h2 : term431 A B op s f g x) : term384 A x s.
Proof. exact (EQ_MP (@lem5976467 A x s) (@lem5976464 A B op s f g x h1 h2)). Qed.
Lemma lem5976474 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5976475 {A B : Type'} (f : A -> B) (g : A -> B) (_75757 : A) (s : A -> Prop) : (term387 A B s f g _75757) = (term462 A B f g _75757 s).
Proof. exact (@lem5976474 ((@I (A -> B) f _75757) = (@I (A -> B) g _75757)) (term385 A _75757 s)). Qed.
Lemma lem5976483 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5976484 {A B : Type'} (f : A -> B) (g : A -> B) (_75757 : A) (s : A -> Prop) : (term463 A B s f g _75757) = (term464 A B f g _75757 s).
Proof. exact (MK_COMB (@lem5976483) (@lem5976475 A B f g _75757 s)). Qed.
Lemma lem5976492 {A B : Type'} (f : A -> B) (g : A -> B) (_75757 : A) (s : A -> Prop) : (term462 A B f g _75757 s) = (term462 A B f g _75757 s).
Proof. exact (eq_refl (term462 A B f g _75757 s)). Qed.
Lemma lem5976493 {A B : Type'} (f : A -> B) (g : A -> B) (_75757 : A) (s : A -> Prop) : ((term387 A B s f g _75757) = (term462 A B f g _75757 s)) = ((term462 A B f g _75757 s) = (term462 A B f g _75757 s)).
Proof. exact (MK_COMB (@lem5976484 A B f g _75757 s) (@lem5976492 A B f g _75757 s)). Qed.
Lemma lem5976495 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5976496 (x : Prop) : (x = x) = True.
Proof. exact (@lem5976495 Prop x). Qed.
Lemma lem5976497 {A B : Type'} (f : A -> B) (g : A -> B) (_75757 : A) (s : A -> Prop) : ((term462 A B f g _75757 s) = (term462 A B f g _75757 s)) = True.
Proof. exact (@lem5976496 (term462 A B f g _75757 s)). Qed.
Lemma lem5976498 {A B : Type'} (f : A -> B) (g : A -> B) (_75757 : A) (s : A -> Prop) : ((term387 A B s f g _75757) = (term462 A B f g _75757 s)) = True.
Proof. exact (TRANS (@lem5976493 A B f g _75757 s) (@lem5976497 A B f g _75757 s)). Qed.
Lemma lem5976499 {A B : Type'} (f : A -> B) (g : A -> B) (_75757 : A) (s : A -> Prop) : True = ((term387 A B s f g _75757) = (term462 A B f g _75757 s)).
Proof. exact (SYM (@lem5976498 A B f g _75757 s)). Qed.
Lemma lem5976500 {A B : Type'} (f : A -> B) (g : A -> B) (_75757 : A) (s : A -> Prop) : (term387 A B s f g _75757) = (term462 A B f g _75757 s).
Proof. exact (EQ_MP (@lem5976499 A B f g _75757 s) (@lem0)). Qed.
Lemma lem5976501 {A B : Type'} (_75757 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term462 A B f g _75757 s.
Proof. exact (EQ_MP (@lem5976500 A B f g _75757 s) (@lem5975645 A B _75757 s f g h1)). Qed.
Lemma lem5976503 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5976504 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_75757 : A) : (term462 A B f g _75757 s) = (term465 A B s f g _75757).
Proof. exact (@lem5976503 (term385 A _75757 s) ((@I (A -> B) f _75757) = (@I (A -> B) g _75757))). Qed.
Lemma lem5976506 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5976507 {A : Type'} (_75757 : A) (s : A -> Prop) : (term466 A _75757 s) = (term384 A _75757 s).
Proof. exact (@lem5976506 (term384 A _75757 s)). Qed.
Lemma lem5976508 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5976509 {A : Type'} (_75757 : A) (s : A -> Prop) : (term467 A _75757 s) = (term468 A _75757 s).
Proof. exact (MK_COMB (@lem5976508) (@lem5976507 A _75757 s)). Qed.
Lemma lem5976510 {A B : Type'} (f : A -> B) (g : A -> B) (_75757 : A) : ((@I (A -> B) f _75757) = (@I (A -> B) g _75757)) = ((@I (A -> B) f _75757) = (@I (A -> B) g _75757)).
Proof. exact (eq_refl ((@I (A -> B) f _75757) = (@I (A -> B) g _75757))). Qed.
Lemma lem5976511 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_75757 : A) : (term465 A B s f g _75757) = (term469 A B s f g _75757).
Proof. exact (MK_COMB (@lem5976509 A _75757 s) (@lem5976510 A B f g _75757)). Qed.
Lemma lem5976512 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_75757 : A) : (term462 A B f g _75757 s) = (term469 A B s f g _75757).
Proof. exact (TRANS (@lem5976504 A B s f g _75757) (@lem5976511 A B s f g _75757)). Qed.
Lemma lem5976515 {A B : Type'} (_75757 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term469 A B s f g _75757.
Proof. exact (EQ_MP (@lem5976512 A B s f g _75757) (@lem5976501 A B _75757 s f g h1)). Qed.
Lemma lem5976516 {A B : Type'} (_75757 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term469 A B s f g _75757.
Proof. exact (@lem5976515 A B _75757 s f g h1). Qed.
Lemma lem5976517 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term469 A B s f g x.
Proof. exact (@lem5976516 A B x s f g h1). Qed.
Lemma lem5976520 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term26 A B s f g) (h2 : term192 A B) (h3 : term431 A B op s f g x) : (@I (A -> B) f x) = (@I (A -> B) g x).
Proof. exact (@lem5976517 A B x s f g h1 (@lem5976468 A B op s f g x h2 h3)). Qed.
Lemma lem5976521 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term26 A B s f g) (h2 : term192 A B) (h3 : term431 A B op s f g x) : term470 A B f g x.
Proof. exact (fun h0 : term428 A B f g x => @lem5976520 A B op s f g x h1 h2 h3). Qed.
Lemma lem5976523 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5976524 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term470 A B f g x) = ((@I (A -> B) f x) = (@I (A -> B) g x)).
Proof. exact (@lem5976523 ((@I (A -> B) f x) = (@I (A -> B) g x))). Qed.
Lemma lem5976525 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term26 A B s f g) (h2 : term192 A B) (h3 : term431 A B op s f g x) : (@I (A -> B) f x) = (@I (A -> B) g x).
Proof. exact (EQ_MP (@lem5976524 A B f g x) (@lem5976521 A B op s f g x h1 h2 h3)). Qed.
Lemma lem5976528 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5976530 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term428 A B f g x) = (term471 A B f g x).
Proof. exact (@lem5976528 ((@I (A -> B) f x) = (@I (A -> B) g x))). Qed.
Lemma lem5976533 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term431 A B op s f g x) : term471 A B f g x.
Proof. exact (EQ_MP (@lem5976530 A B f g x) (@lem5975681 A B op s f g x h1)). Qed.
Lemma lem5976536 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term26 A B s f g) (h2 : term192 A B) (h3 : term431 A B op s f g x) : False.
Proof. exact (@lem5976533 A B op s f g x h3 (@lem5976525 A B op s f g x h1 h2 h3)). Qed.
Lemma lem5976537 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term26 A B s f g) (h2 : term192 A B) (h3 : term431 A B op s f g x) : term103.
Proof. exact (fun h0 : ~ False => @lem5976536 A B op s f g x h1 h2 h3). Qed.
Lemma lem5976539 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5976540 : term103 = False.
Proof. exact (@lem5976539 False). Qed.
Lemma lem5976541 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term26 A B s f g) (h2 : term192 A B) (h3 : term431 A B op s f g x) : False.
Proof. exact (EQ_MP (@lem5976540) (@lem5976537 A B op s f g x h1 h2 h3)). Qed.
Lemma lem5976542 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) (h2 : term432 A B op f s) : (term432 A B op f s) = False.
Proof. exact (prop_ext (fun h3 : term432 A B op f s => @lem5976074 A B op f s h1 h2) (fun h3 : False => @lem5975601 A B op f s h2)). Qed.
Lemma lem5976543 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) (h2 : term432 A B op f s) : False.
Proof. exact (EQ_MP (@lem5976542 A B op f s h1 h2) (@lem5975601 A B op f s h2)). Qed.
Lemma lem5976544 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) (h2 : term432 A B op f s) : (term432 A B op f s) = False.
Proof. exact (prop_ext (fun h3 : term432 A B op f s => @lem5976543 A B op f s h1 h2) (fun h3 : False => @lem5975188 A B op f s h2)). Qed.
Lemma lem5976545 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) (h2 : term432 A B op f s) : False.
Proof. exact (EQ_MP (@lem5976544 A B op f s h1 h2) (@lem5975188 A B op f s h2)). Qed.
Lemma lem5976546 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) (h2 : term432 A B op f s) : (term432 A B op f s) = False.
Proof. exact (prop_ext (fun h3 : term432 A B op f s => @lem5976545 A B op f s h1 h2) (fun h3 : False => @lem5975188 A B op f s h2)). Qed.
Lemma lem5976547 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term157 A B op f s) (h2 : term432 A B op f s) : False.
Proof. exact (EQ_MP (@lem5976546 A B op f s h1 h2) (@lem5975188 A B op f s h2)). Qed.
Lemma lem5976548 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term26 A B s f g) (h2 : term192 A B) (h3 : term157 A B op f s) (h4 : term268 A B op s f g x) : False.
Proof. exact (or_elim (@lem5974973 A B op s f g x h4) (fun h0 : term432 A B op f s => @lem5976547 A B op f s h3 h0) (fun h0 : term431 A B op s f g x => @lem5976541 A B op s f g x h1 h2 h0)). Qed.
Lemma lem5976549 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term192 A B) (h3 : term157 A B op f s) (h4 : term190 A B op s f g) : False.
Proof. exact (ex_elim (@lem5972360 A B op s f g h4) (fun x : A => fun h0 : term270 A B op s f g x => @lem5976548 A B op s f g x h1 h2 h3 h0)). Qed.
Lemma lem5976550 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term192 A B) (h3 : term157 A B op f s) (h4 : term190 A B op s f g) : (term157 A B op f s) = False.
Proof. exact (prop_ext (fun h5 : term157 A B op f s => @lem5976549 A B op s f g h1 h2 h3 h4) (fun h5 : False => @lem5972265 A B op f s h3)). Qed.
Lemma lem5976551 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term192 A B) (h3 : term157 A B op f s) (h4 : term190 A B op s f g) : False.
Proof. exact (EQ_MP (@lem5976550 A B op s f g h1 h2 h3 h4) (@lem5972265 A B op f s h3)). Qed.
Lemma lem5976552 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : term190 A B op s f g) : term197 A B.
Proof. exact (fun h0 : term192 A B => @lem5976551 A B op s f g h1 h0 h2 h3). Qed.
Lemma lem5976553 {A B : Type'} : (term197 A B) = (term198 A B).
Proof. exact (@lem69 (term192 A B)). Qed.
Lemma lem5976554 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : term190 A B op s f g) : term198 A B.
Proof. exact (EQ_MP (@lem5976553 A B) (@lem5976552 A B op s f g h1 h2 h3)). Qed.
Lemma lem5976555 {_119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : term190 A B op s f g) : term201 _119829 A B.
Proof. exact (fun h0 : term192 _119829 B => @lem5976554 A B op s f g h1 h2 h3). Qed.
Lemma lem5976556 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : term190 A B op s f g) : term204 _119826 _119829 A B.
Proof. exact (fun h0 : term191 _119826 A => @lem5976555 _119829 A B op s f g h1 h2 h3). Qed.
Lemma lem5976557 {_119826 _119829 A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term26 A B s f g) (h2 : term157 A B op f s) : term207 _119826 _119829 A B op s f g.
Proof. exact (fun h0 : term190 A B op s f g => @lem5976556 _119826 _119829 A B op s f g h1 h2 h0). Qed.
Lemma lem5976558 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) : term209 _119826 _119829 A B op s f g.
Proof. exact (fun h0 : term157 A B op f s => @lem5976557 _119826 _119829 A B g op f s h1 h0). Qed.
Lemma lem5976559 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : term211 _119826 _119829 A B op s f g.
Proof. exact (fun h0 : term26 A B s f g => @lem5976558 _119826 _119829 A B op s f g h0). Qed.
Lemma lem5976560 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : term212 _119826 _119829 A B op s f g.
Proof. exact (fun h0 : @monoidal B op => @lem5976559 _119826 _119829 A B op s f g). Qed.
Lemma lem5976565 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term216 _119826 _119829 A B s f g.
Proof. exact (fun op : type1400 B => @lem5976560 _119826 _119829 A B op s f g). Qed.
Lemma lem5976570 {_119826 _119829 A B : Type'} (f : A -> B) (g : A -> B) : term220 _119826 _119829 A B f g.
Proof. exact (fun s : A -> Prop => @lem5976565 _119826 _119829 A B s f g). Qed.
Lemma lem5976575 {_119826 _119829 A B : Type'} (g : A -> B) : term224 _119826 _119829 A B g.
Proof. exact (fun f : A -> B => @lem5976570 _119826 _119829 A B f g). Qed.
Lemma lem5976580 {_119826 _119829 A B : Type'} : term228 _119826 _119829 A B.
Proof. exact (fun g : A -> B => @lem5976575 _119826 _119829 A B g). Qed.
Lemma lem5976581 {_119826 _119829 A B : Type'} : term227 _119826 _119829 A B.
Proof. exact (EQ_MP (@lem5972183 _119826 _119829 A B) (@lem5976580 _119826 _119829 A B)). Qed.
Lemma lem5976582 {_119826 _119829 A B : Type'} (g : A -> B) : term472 _119826 _119829 A B g.
Proof. exact (@lem5976581 _119826 _119829 A B g). Qed.
Lemma lem5976583 {_119826 _119829 A B : Type'} (g : A -> B) : (term472 _119826 _119829 A B g) = (term223 _119826 _119829 A B g).
Proof. exact (eq_refl (term472 _119826 _119829 A B g)). Qed.
Lemma lem5976584 {_119826 _119829 A B : Type'} (g : A -> B) : term223 _119826 _119829 A B g.
Proof. exact (EQ_MP (@lem5976583 _119826 _119829 A B g) (@lem5976582 _119826 _119829 A B g)). Qed.
Lemma lem5976585 {_119826 _119829 A B : Type'} (g : A -> B) (f : A -> B) : term473 _119826 _119829 A B g f.
Proof. exact (@lem5976584 _119826 _119829 A B g f). Qed.
Lemma lem5976586 {_119826 _119829 A B : Type'} (f : A -> B) (g : A -> B) : (term473 _119826 _119829 A B g f) = (term219 _119826 _119829 A B f g).
Proof. exact (eq_refl (term473 _119826 _119829 A B g f)). Qed.
Lemma lem5976587 {_119826 _119829 A B : Type'} (f : A -> B) (g : A -> B) : term219 _119826 _119829 A B f g.
Proof. exact (EQ_MP (@lem5976586 _119826 _119829 A B f g) (@lem5976585 _119826 _119829 A B g f)). Qed.
Lemma lem5976588 {_119826 _119829 A B : Type'} (f : A -> B) (g : A -> B) (s : A -> Prop) : term474 _119826 _119829 A B f g s.
Proof. exact (@lem5976587 _119826 _119829 A B f g s). Qed.
Lemma lem5976589 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term474 _119826 _119829 A B f g s) = (term215 _119826 _119829 A B s f g).
Proof. exact (eq_refl (term474 _119826 _119829 A B f g s)). Qed.
Lemma lem5976590 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term215 _119826 _119829 A B s f g.
Proof. exact (EQ_MP (@lem5976589 _119826 _119829 A B s f g) (@lem5976588 _119826 _119829 A B f g s)). Qed.
Lemma lem5976591 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) : term475 _119826 _119829 A B s f g op.
Proof. exact (@lem5976590 _119826 _119829 A B s f g op). Qed.
Lemma lem5976592 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term475 _119826 _119829 A B s f g op) = (term193 _119826 _119829 A B op s f g).
Proof. exact (eq_refl (term475 _119826 _119829 A B s f g op)). Qed.
Lemma lem5976593 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : term193 _119826 _119829 A B op s f g.
Proof. exact (EQ_MP (@lem5976592 _119826 _119829 A B op s f g) (@lem5976591 _119826 _119829 A B s f g op)). Qed.
Lemma lem5976595 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) : term193 _119826 _119829 A B op s f g.
Proof. exact (@lem5971767 _119826 _119829 A B op s f g (@lem5976593 _119826 _119829 A B op s f g)). Qed.
Lemma lem5976596 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term210 _119826 _119829 A B op s f g.
Proof. exact (@lem5976595 _119826 _119829 A B op s f g (@lem5970116 B op h1)). Qed.
Lemma lem5976597 {_119826 _119829 A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : term208 _119826 _119829 A B op s f g.
Proof. exact (@lem5976596 _119826 _119829 A B s f g op h2 (@lem5970117 A B s f g h1)). Qed.
Lemma lem5976598 {_119826 _119829 A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) : term206 _119826 _119829 A B op s f g.
Proof. exact (@lem5976597 _119826 _119829 A B s f g op h1 h3 (@lem5971667 A B op f s h2)). Qed.
Lemma lem5976599 {_119826 _119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) (h4 : term190 A B op s f g) : term203 _119826 _119829 A B.
Proof. exact (@lem5976598 _119826 _119829 A B g f s op h1 h2 h3 (@lem5971748 A B op s f g h4)). Qed.
Lemma lem5976600 {_119829 A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) (h4 : term190 A B op s f g) : term200 _119829 A B.
Proof. exact (@lem5976599 Prop _119829 A B op s f g h1 h2 h3 h4 (@lem5971749 Prop A)). Qed.
Lemma lem5976601 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) (h4 : term190 A B op s f g) : term197 A B.
Proof. exact (@lem5976600 Prop A B op s f g h1 h2 h3 h4 (@lem5971751 Prop B)). Qed.
Lemma lem5976602 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) (h4 : term190 A B op s f g) : False.
Proof. exact (@lem5976601 A B op s f g h1 h2 h3 h4 (@lem5971750 A B)). Qed.
Lemma lem5976603 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) (h4 : term190 A B op s f g) : (term190 A B op s f g) = False.
Proof. exact (prop_ext (fun h5 : term190 A B op s f g => @lem5976602 A B op s f g h1 h2 h3 h4) (fun h5 : False => @lem5971748 A B op s f g h4)). Qed.
Lemma lem5976604 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) (h4 : term190 A B op s f g) : False.
Proof. exact (EQ_MP (@lem5976603 A B op s f g h1 h2 h3 h4) (@lem5971748 A B op s f g h4)). Qed.
Lemma lem5976605 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) : term189 A B op s f g.
Proof. exact (fun h0 : term190 A B op s f g => @lem5976604 A B op s f g h1 h2 h3 h0). Qed.
Lemma lem5976606 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) : term188 A B op s f g.
Proof. exact (EQ_MP (@lem5971747 A B op s f g) (@lem5976605 A B g f s op h1 h2 h3)). Qed.
Lemma lem5976608 (p : Prop) (q : Prop) (r : Prop) : (term476 p q r) = (term477 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem5976609 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (g : A -> B) : (term478 A B op f s g) = (term479 A B op f s g).
Proof. exact (@lem5976608 (term157 A B op f s) (term242 A B op s f g) ((term156 A B op s f) = (term185 A B op f s g))). Qed.
Lemma lem5976624 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (g : A -> B) : (term479 A B op f s g) = (term478 A B op f s g).
Proof. exact (SYM (@lem5976609 A B op f s g)). Qed.
Lemma lem5976626 {A : Type'} (P : type686 A) : term2 A P.
Proof. exact (EQ_MP (@lem5970067 A P) (@lem5970066 A P)). Qed.
Lemma lem5976627 {A : Type'} (P : type686 A) : term2 A P.
Proof. exact (@lem5976626 A P). Qed.
Lemma lem5976628 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : term480 A B f op g.
Proof. exact (@lem5976627 A (term481 A B f op g)). Qed.
Lemma lem5976629 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term482 A B f op g) = (term483 A B f op g).
Proof. exact (eq_refl (term482 A B f op g)). Qed.
Lemma lem5976630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5976631 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term484 A B f op g) = (term485 A B f op g).
Proof. exact (MK_COMB (@lem5976630) (@lem5976629 A B f op g)). Qed.
Lemma lem5976632 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term486 A B f op g t) = (term487 A B f op t g).
Proof. exact (eq_refl (term486 A B f op g t)). Qed.
Lemma lem5976633 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5976634 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term488 A B f op g t) = (term489 A B f op t g).
Proof. exact (MK_COMB (@lem5976633) (@lem5976632 A B f op t g)). Qed.
Lemma lem5976635 {A : Type'} (x : A) (t : A -> Prop) : (term490 A x t) = (term490 A x t).
Proof. exact (eq_refl (term490 A x t)). Qed.
Lemma lem5976636 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term491 A B f op g x t) = (term492 A B f op g x t).
Proof. exact (MK_COMB (@lem5976634 A B f op t g) (@lem5976635 A x t)). Qed.
Lemma lem5976637 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5976638 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term493 A B f op g x t) = (term494 A B f op g x t).
Proof. exact (MK_COMB (@lem5976637) (@lem5976636 A B f op g x t)). Qed.
Lemma lem5976639 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) : (term495 A B f op g x t) = (term496 A B f op x t g).
Proof. exact (eq_refl (term495 A B f op g x t)). Qed.
Lemma lem5976640 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) : (term497 A B f op g x t) = (term498 A B f op x t g).
Proof. exact (MK_COMB (@lem5976638 A B f op g x t) (@lem5976639 A B f op x t g)). Qed.
Lemma lem5976641 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (g : A -> B) : (term499 A B f op g x) = (term500 A B f op x g).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5976640 A B f op x t g)). Qed.
Lemma lem5976642 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5976643 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (g : A -> B) : (term501 A B f op g x) = (term502 A B f op x g).
Proof. exact (MK_COMB (@lem5976642 A) (@lem5976641 A B f op x g)). Qed.
Lemma lem5976644 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term503 A B f op g) = (term504 A B f op g).
Proof. exact (fun_ext (fun x : A => @lem5976643 A B f op x g)). Qed.
Lemma lem5976645 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5976646 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term505 A B f op g) = (term506 A B f op g).
Proof. exact (MK_COMB (@lem5976645 A) (@lem5976644 A B f op g)). Qed.
Lemma lem5976647 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term507 A B f op g) = (term508 A B f op g).
Proof. exact (MK_COMB (@lem5976631 A B f op g) (@lem5976646 A B f op g)). Qed.
Lemma lem5976648 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5976649 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term509 A B f op g) = (term510 A B f op g).
Proof. exact (MK_COMB (@lem5976648) (@lem5976647 A B f op g)). Qed.
Lemma lem5976650 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term486 A B f op g t) = (term487 A B f op t g).
Proof. exact (eq_refl (term486 A B f op g t)). Qed.
Lemma lem5976651 {A : Type'} (t : A -> Prop) : (term511 A t) = (term511 A t).
Proof. exact (eq_refl (term511 A t)). Qed.
Lemma lem5976652 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term512 A B f op g t) = (term513 A B f op t g).
Proof. exact (MK_COMB (@lem5976651 A t) (@lem5976650 A B f op t g)). Qed.
Lemma lem5976653 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term514 A B f op g) = (term515 A B f op g).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5976652 A B f op t g)). Qed.
Lemma lem5976654 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5976655 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term516 A B f op g) = (term517 A B f op g).
Proof. exact (MK_COMB (@lem5976654 A) (@lem5976653 A B f op g)). Qed.
Lemma lem5976656 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term480 A B f op g) = (term518 A B f op g).
Proof. exact (MK_COMB (@lem5976649 A B f op g) (@lem5976655 A B f op g)). Qed.
Lemma lem5976657 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : term518 A B f op g.
Proof. exact (EQ_MP (@lem5976656 A B f op g) (@lem5976628 A B f op g)). Qed.
Lemma lem5976658 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term519 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem5976659 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term519 _120477 _120519 _120521 op) = (term520 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term519 _120477 _120519 _120521 op)). Qed.
Lemma lem5976660 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term520 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem5976659 _120477 _120519 _120521 op) (@lem5976658 _120477 _120519 _120521 op)). Qed.
Lemma lem5976661 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem5976662 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term521 _120477 _120519 _120521 op.
Proof. exact (@lem5976660 _120477 _120519 _120521 op (@lem5976661 _120519 op h1)). Qed.
Lemma lem5976663 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term522 _120519 _120521 op.
Proof. exact (proj2 (@lem5976662 Prop _120519 _120521 op h1)). Qed.
Lemma lem5976664 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term523 _120519 _120521 op f.
Proof. exact (@lem5976663 _120519 _120521 op h1 f). Qed.
Lemma lem5976665 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term523 _120519 _120521 op f) = (term524 _120519 _120521 op f).
Proof. exact (eq_refl (term523 _120519 _120521 op f)). Qed.
Lemma lem5976666 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term524 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem5976665 _120519 _120521 op f) (@lem5976664 _120519 _120521 f op h1)). Qed.
Lemma lem5976667 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term525 _120519 _120521 op f x.
Proof. exact (@lem5976666 _120519 _120521 f op h1 x). Qed.
Lemma lem5976668 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term525 _120519 _120521 op f x) = (term526 _120519 _120521 x op f).
Proof. exact (eq_refl (term525 _120519 _120521 op f x)). Qed.
Lemma lem5976669 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term526 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem5976668 _120519 _120521 x op f) (@lem5976667 _120519 _120521 f x op h1)). Qed.
Lemma lem5976670 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term527 _120519 _120521 x op f s.
Proof. exact (@lem5976669 _120519 _120521 x f op h1 s). Qed.
Lemma lem5976671 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term527 _120519 _120521 x op f s) = (term528 _120519 _120521 x op s f).
Proof. exact (eq_refl (term527 _120519 _120521 x op f s)). Qed.
Lemma lem5976672 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term528 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5976671 _120519 _120521 x op s f) (@lem5976670 _120519 _120521 x f s op h1)). Qed.
Lemma lem5976673 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem5976674 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term529 _120519 _120521 op x s f) = (term530 _120519 _120521 x op s f).
Proof. exact (@lem5976672 _120519 _120521 x s f op h2 (@lem5976673 _120521 s h1)). Qed.
Lemma lem5976675 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term531 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5976674 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem5976676 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term532 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem5976675 _120519 _120521 x op f s h0). Qed.
Lemma lem5976678 (p : Prop) (q : Prop) (r : Prop) : (term477 p q r) = (term476 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5976683 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term532 _120519 _120521 x op s f) = (term533 _120519 _120521 x op s f).
Proof. exact (@lem5976678 (@FINITE _120521 s) (@monoidal _120519 op) ((term529 _120519 _120521 op x s f) = (term530 _120519 _120521 x op s f))). Qed.
Lemma lem5976685 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term534 _120477 _120519 op.
Proof. exact (proj1 (@lem5976662 _120477 _120519 Prop op h1)). Qed.
Lemma lem5976686 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term535 _120477 _120519 op f.
Proof. exact (@lem5976685 _120477 _120519 op h1 f). Qed.
Lemma lem5976687 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term535 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term535 _120477 _120519 op f)). Qed.
Lemma lem5976688 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem5976687 _120477 _120519 f op) (@lem5976686 _120477 _120519 f op h1)). Qed.
Lemma lem5976694 {B : Type'} (op : type1400 B) : (@monoidal B op) = ((@monoidal B op) = True).
Proof. exact (@lem7 (@monoidal B op)). Qed.
Lemma lem5976713 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term536 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5976714 (p : Prop) (q : Prop) (p' : Prop) : term537 p q p'.
Proof. exact (fun q' : Prop => @lem5976713 p q p' q'). Qed.
Lemma lem5976715 (p : Prop) (q : Prop) : term538 p q.
Proof. exact (fun p' : Prop => @lem5976714 p q p'). Qed.
Lemma lem5976716 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : term539 A B f op g.
Proof. exact (@lem5976715 (term540 A B f g) ((@iterate B A op (@EMPTY A) f) = (@iterate B A op (@EMPTY A) g))). Qed.
Lemma lem5976717 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (p' : Prop) : term541 A B f op g p'.
Proof. exact (@lem5976716 A B f op g p'). Qed.
Lemma lem5976718 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (p' : Prop) : (term541 A B f op g p') = (term542 A B f op g p').
Proof. exact (eq_refl (term541 A B f op g p')). Qed.
Lemma lem5976719 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (p' : Prop) : term542 A B f op g p'.
Proof. exact (EQ_MP (@lem5976718 A B f op g p') (@lem5976717 A B f op g p')). Qed.
Lemma lem5976720 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (p' : Prop) (q' : Prop) : term543 A B f op g p' q'.
Proof. exact (@lem5976719 A B f op g p' q'). Qed.
Lemma lem5976721 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (p' : Prop) (q' : Prop) : (term543 A B f op g p' q') = (term544 A B f op g p' q').
Proof. exact (eq_refl (term543 A B f op g p' q')). Qed.
Lemma lem5976722 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (p' : Prop) (q' : Prop) : term544 A B f op g p' q'.
Proof. exact (EQ_MP (@lem5976721 A B f op g p' q') (@lem5976720 A B f op g p' q')). Qed.
Lemma lem5976764 {A B : Type'} (f : A -> B) (g : A -> B) : (term540 A B f g) = (term540 A B f g).
Proof. exact (eq_refl (term540 A B f g)). Qed.
Lemma lem5976765 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (q' : Prop) : term545 A B op f g q'.
Proof. exact (@lem5976722 A B f op g (term540 A B f g) q'). Qed.
Lemma lem5976766 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) (q' : Prop) : term546 A B op f g q'.
Proof. exact (@lem5976765 A B op f g q' (@lem5976764 A B f g)). Qed.
Lemma lem5976781 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term547 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5976688 _120477 _120519 f op h0). Qed.
Lemma lem5976782 {A B : Type'} (f : A -> B) (op : type1400 B) : term547 A B f op.
Proof. exact (@lem5976781 A B f op). Qed.
Lemma lem5976784 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5976694 B op) (@lem5970116 B op h1)). Qed.
Lemma lem5976785 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : True = (@monoidal B op).
Proof. exact (SYM (@lem5976784 B op h1)). Qed.
Lemma lem5976786 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (EQ_MP (@lem5976785 B op h1) (@lem0)). Qed.
Lemma lem5976787 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (@iterate B A op (@EMPTY A) f) = (@neutral B op).
Proof. exact (@lem5976782 A B f op (@lem5976786 B op h1)). Qed.
Lemma lem5976788 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5976789 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term548 A B op f) = (term187 B op).
Proof. exact (MK_COMB (@lem5976788 B) (@lem5976787 A B f op h1)). Qed.
Lemma lem5976791 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term547 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5976688 _120477 _120519 f op h0). Qed.
Lemma lem5976792 {A B : Type'} (f : A -> B) (op : type1400 B) : term547 A B f op.
Proof. exact (@lem5976791 A B f op). Qed.
Lemma lem5976793 {A B : Type'} (g : A -> B) (op : type1400 B) : term547 A B g op.
Proof. exact (@lem5976792 A B g op). Qed.
Lemma lem5976795 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5976694 B op) (@lem5970116 B op h1)). Qed.
Lemma lem5976796 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : True = (@monoidal B op).
Proof. exact (SYM (@lem5976795 B op h1)). Qed.
Lemma lem5976797 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (EQ_MP (@lem5976796 B op h1) (@lem0)). Qed.
Lemma lem5976798 {A B : Type'} (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (@iterate B A op (@EMPTY A) g) = (@neutral B op).
Proof. exact (@lem5976793 A B g op (@lem5976797 B op h1)). Qed.
Lemma lem5976799 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : ((@iterate B A op (@EMPTY A) f) = (@iterate B A op (@EMPTY A) g)) = ((@neutral B op) = (@neutral B op)).
Proof. exact (MK_COMB (@lem5976789 A B f op h1) (@lem5976798 A B g op h1)). Qed.
Lemma lem5976801 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5976802 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem5976801 B x). Qed.
Lemma lem5976803 {B : Type'} (op : type1400 B) : ((@neutral B op) = (@neutral B op)) = True.
Proof. exact (@lem5976802 B (@neutral B op)). Qed.
Lemma lem5976804 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : ((@iterate B A op (@EMPTY A) f) = (@iterate B A op (@EMPTY A) g)) = True.
Proof. exact (TRANS (@lem5976799 A B f g op h1) (@lem5976803 B op)). Qed.
Lemma lem5976805 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term549 A B f op g.
Proof. exact (fun h0 : term540 A B f g => @lem5976804 A B f g op h1). Qed.
Lemma lem5976806 {A B : Type'} (op : type1400 B) (f : A -> B) (g : A -> B) : term550 A B op f g.
Proof. exact (@lem5976766 A B op f g True). Qed.
Lemma lem5976807 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term483 A B f op g) = (term551 A B f g).
Proof. exact (@lem5976806 A B op f g (@lem5976805 A B f g op h1)). Qed.
Lemma lem5976809 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5976810 {A B : Type'} (f : A -> B) (g : A -> B) : (term551 A B f g) = True.
Proof. exact (@lem5976809 (term540 A B f g)). Qed.
Lemma lem5976811 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term483 A B f op g) = True.
Proof. exact (TRANS (@lem5976807 A B f g op h1) (@lem5976810 A B f g)). Qed.
Lemma lem5976812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5976813 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term485 A B f op g) = (and True).
Proof. exact (MK_COMB (@lem5976812) (@lem5976811 A B f g op h1)). Qed.
Lemma lem5976825 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term536 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5976826 (p : Prop) (q : Prop) (p' : Prop) : term537 p q p'.
Proof. exact (fun q' : Prop => @lem5976825 p q p' q'). Qed.
Lemma lem5976827 (p : Prop) (q : Prop) : term538 p q.
Proof. exact (fun p' : Prop => @lem5976826 p q p'). Qed.
Lemma lem5976828 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) : term552 A B f op x t g.
Proof. exact (@lem5976827 (term492 A B f op g x t) (term496 A B f op x t g)). Qed.
Lemma lem5976829 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term553 A B f op x t g p'.
Proof. exact (@lem5976828 A B f op x t g p'). Qed.
Lemma lem5976830 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : (term553 A B f op x t g p') = (term554 A B f op x t g p').
Proof. exact (eq_refl (term553 A B f op x t g p')). Qed.
Lemma lem5976831 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term554 A B f op x t g p'.
Proof. exact (EQ_MP (@lem5976830 A B f op x t g p') (@lem5976829 A B f op x t g p')). Qed.
Lemma lem5976832 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term555 A B f op x t g p' q'.
Proof. exact (@lem5976831 A B f op x t g p' q'). Qed.
Lemma lem5976833 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : (term555 A B f op x t g p' q') = (term556 A B f op x t g p' q').
Proof. exact (eq_refl (term555 A B f op x t g p' q')). Qed.
Lemma lem5976834 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term556 A B f op x t g p' q'.
Proof. exact (EQ_MP (@lem5976833 A B f op x t g p' q') (@lem5976832 A B f op x t g p' q')). Qed.
Lemma lem5976956 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term492 A B f op g x t) = (term492 A B f op g x t).
Proof. exact (eq_refl (term492 A B f op g x t)). Qed.
Lemma lem5976957 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (q' : Prop) : term557 A B f op g x t q'.
Proof. exact (@lem5976834 A B f op x t g (term492 A B f op g x t) q'). Qed.
Lemma lem5976958 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (q' : Prop) : term558 A B f op g x t q'.
Proof. exact (@lem5976957 A B f op g x t q' (@lem5976956 A B f op g x t)). Qed.
Lemma lem5976959 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : term492 A B f op g x t.
Proof. exact (h1). Qed.
Lemma lem5976960 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : term490 A x t.
Proof. exact (proj2 (@lem5976959 A B f op g x t h1)). Qed.
Lemma lem5976961 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : @FINITE A t.
Proof. exact (proj2 (@lem5976960 A B f op g x t h1)). Qed.
Lemma lem5976962 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem5976964 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : term98 A x t.
Proof. exact (proj1 (@lem5976960 A B f op g x t h1)). Qed.
Lemma lem5976965 {A : Type'} (x : A) (t : A -> Prop) : term559 A x t.
Proof. exact (@lem82 (@IN A x t)). Qed.
Lemma lem5976978 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term536 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5976979 (p : Prop) (q : Prop) (p' : Prop) : term537 p q p'.
Proof. exact (fun q' : Prop => @lem5976978 p q p' q'). Qed.
Lemma lem5976980 (p : Prop) (q : Prop) : term538 p q.
Proof. exact (fun p' : Prop => @lem5976979 p q p'). Qed.
Lemma lem5976981 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) : term560 A B f op x t g.
Proof. exact (@lem5976980 (term561 A B x t f g) ((term562 A B op x t f) = (term562 A B op x t g))). Qed.
Lemma lem5976982 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term563 A B f op x t g p'.
Proof. exact (@lem5976981 A B f op x t g p'). Qed.
Lemma lem5976983 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : (term563 A B f op x t g p') = (term564 A B f op x t g p').
Proof. exact (eq_refl (term563 A B f op x t g p')). Qed.
Lemma lem5976984 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) (p' : Prop) : term564 A B f op x t g p'.
Proof. exact (EQ_MP (@lem5976983 A B f op x t g p') (@lem5976982 A B f op x t g p')). Qed.
Lemma lem5976985 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term565 A B f op x t g p' q'.
Proof. exact (@lem5976984 A B f op x t g p' q'). Qed.
Lemma lem5976986 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : (term565 A B f op x t g p' q') = (term566 A B f op x t g p' q').
Proof. exact (eq_refl (term565 A B f op x t g p' q')). Qed.
Lemma lem5976987 {A B : Type'} (f : A -> B) (op : type1400 B) (x : A) (t : A -> Prop) (g : A -> B) (p' : Prop) (q' : Prop) : term566 A B f op x t g p' q'.
Proof. exact (EQ_MP (@lem5976986 A B f op x t g p' q') (@lem5976985 A B f op x t g p' q')). Qed.
Lemma lem5977031 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term561 A B x t f g) = (term561 A B x t f g).
Proof. exact (eq_refl (term561 A B x t f g)). Qed.
Lemma lem5977032 {A B : Type'} (op : type1400 B) (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (q' : Prop) : term567 A B op x t f g q'.
Proof. exact (@lem5976987 A B f op x t g (term561 A B x t f g) q'). Qed.
Lemma lem5977033 {A B : Type'} (op : type1400 B) (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (q' : Prop) : term568 A B op x t f g q'.
Proof. exact (@lem5977032 A B op x t f g q' (@lem5977031 A B x t f g)). Qed.
Lemma lem5977048 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term533 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5976683 _120519 _120521 x op s f) (@lem5976676 _120519 _120521 x op s f)). Qed.
Lemma lem5977049 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term569 A B x op s f.
Proof. exact (@lem5977048 B A x op s f). Qed.
Lemma lem5977050 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term569 A B x op t f.
Proof. exact (@lem5977049 A B x op t f). Qed.
Lemma lem5977054 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem5976962 A t) (@lem5976961 A B f op g x t h1)). Qed.
Lemma lem5977055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5977056 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : (term570 A t) = (and True).
Proof. exact (MK_COMB (@lem5977055) (@lem5977054 A B f op g x t h1)). Qed.
Lemma lem5977058 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5976694 B op) (@lem5970116 B op h1)). Qed.
Lemma lem5977059 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : (term571 A B t op) = (True /\ True).
Proof. exact (MK_COMB (@lem5977056 A B f op g x t h2) (@lem5977058 B op h1)). Qed.
Lemma lem5977061 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5977062 : (True /\ True) = True.
Proof. exact (@lem5977061 True). Qed.
Lemma lem5977063 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : (term571 A B t op) = True.
Proof. exact (TRANS (@lem5977059 A B f op g x t h1 h2) (@lem5977062)). Qed.
Lemma lem5977064 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : True = (term571 A B t op).
Proof. exact (SYM (@lem5977063 A B f op g x t h1 h2)). Qed.
Lemma lem5977065 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : term571 A B t op.
Proof. exact (EQ_MP (@lem5977064 A B f op g x t h1 h2) (@lem0)). Qed.
Lemma lem5977066 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : (term562 A B op x t f) = (term572 A B x op t f).
Proof. exact (@lem5977050 A B x op t f (@lem5977065 A B f op g x t h1 h2)). Qed.
Lemma lem5977068 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term573 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5977069 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term574 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5977068 _2963 g t e g' t' e'). Qed.
Lemma lem5977070 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term575 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5977069 _2963 g t e g' t'). Qed.
Lemma lem5977071 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term576 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5977070 _2963 g t e g'). Qed.
Lemma lem5977072 {B : Type'} (g : Prop) (t : B) (e : B) : term576 B g t e.
Proof. exact (@lem5977071 B g t e). Qed.
Lemma lem5977073 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term577 A B x op t f.
Proof. exact (@lem5977072 B (@IN A x t) (@iterate B A op t f) (term578 A B x op t f)). Qed.
Lemma lem5977074 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) : term579 A B x op t f g'.
Proof. exact (@lem5977073 A B x op t f g'). Qed.
Lemma lem5977075 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) : (term579 A B x op t f g') = (term580 A B x op t f g').
Proof. exact (eq_refl (term579 A B x op t f g')). Qed.
Lemma lem5977076 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) : term580 A B x op t f g'.
Proof. exact (EQ_MP (@lem5977075 A B x op t f g') (@lem5977074 A B x op t f g')). Qed.
Lemma lem5977077 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : term581 A B x op t f g' t'.
Proof. exact (@lem5977076 A B x op t f g' t'). Qed.
Lemma lem5977078 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : (term581 A B x op t f g' t') = (term582 A B x op t f g' t').
Proof. exact (eq_refl (term581 A B x op t f g' t')). Qed.
Lemma lem5977079 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : term582 A B x op t f g' t'.
Proof. exact (EQ_MP (@lem5977078 A B x op t f g' t') (@lem5977077 A B x op t f g' t')). Qed.
Lemma lem5977080 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : term583 A B x op t f g' t' e'.
Proof. exact (@lem5977079 A B x op t f g' t' e'). Qed.
Lemma lem5977081 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : (term583 A B x op t f g' t' e') = (term584 A B x op t f g' t' e').
Proof. exact (eq_refl (term583 A B x op t f g' t' e')). Qed.
Lemma lem5977082 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : term584 A B x op t f g' t' e'.
Proof. exact (EQ_MP (@lem5977081 A B x op t f g' t' e') (@lem5977080 A B x op t f g' t' e')). Qed.
Lemma lem5977084 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : (@IN A x t) = False.
Proof. exact (@lem5976965 A x t (@lem5976964 A B f op g x t h1)). Qed.
Lemma lem5977085 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (t' : B) (e' : B) : term585 A B x op t f t' e'.
Proof. exact (@lem5977082 A B x op t f False t' e'). Qed.
Lemma lem5977086 {A B : Type'} (t' : B) (e' : B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : term586 A B x op t f t' e'.
Proof. exact (@lem5977085 A B x op t f t' e' (@lem5977084 A B f op g x t h1)). Qed.
Lemma lem5977208 {A B : Type'} (op : type1400 B) (t : A -> Prop) (f : A -> B) : (@iterate B A op t f) = (@iterate B A op t f).
Proof. exact (eq_refl (@iterate B A op t f)). Qed.
Lemma lem5977209 {A B : Type'} (op : type1400 B) (t : A -> Prop) (f : A -> B) : term587 A B op t f.
Proof. exact (fun h0 : False => @lem5977208 A B op t f). Qed.
Lemma lem5977210 {A B : Type'} (e' : B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : term588 A B x op t f e'.
Proof. exact (@lem5977086 A B (@iterate B A op t f) e' f op g x t h1). Qed.
Lemma lem5977211 {A B : Type'} (e' : B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : term589 A B x op t f e'.
Proof. exact (@lem5977210 A B e' f op g x t h1 (@lem5977209 A B op t f)). Qed.
Lemma lem5977330 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term578 A B x op t f) = (term578 A B x op t f).
Proof. exact (eq_refl (term578 A B x op t f)). Qed.
Lemma lem5977331 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term590 A B x op t f.
Proof. exact (fun h0 : ~ False => @lem5977330 A B x op t f). Qed.
Lemma lem5977332 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : term591 A B x op t f.
Proof. exact (@lem5977211 A B (term578 A B x op t f) f op g x t h1). Qed.
Lemma lem5977333 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : (term572 A B x op t f) = (term592 A B x op t f).
Proof. exact (@lem5977332 A B f op g x t h1 (@lem5977331 A B x op t f)). Qed.
Lemma lem5977335 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5977336 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5977335 B t1 t2). Qed.
Lemma lem5977337 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term592 A B x op t f) = (term578 A B x op t f).
Proof. exact (@lem5977336 B (@iterate B A op t f) (term578 A B x op t f)). Qed.
Lemma lem5977449 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : (term572 A B x op t f) = (term578 A B x op t f).
Proof. exact (TRANS (@lem5977333 A B f op g x t h1) (@lem5977337 A B x op t f)). Qed.
Lemma lem5977450 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : (term562 A B op x t f) = (term578 A B x op t f).
Proof. exact (TRANS (@lem5977066 A B f op g x t h1 h2) (@lem5977449 A B f op g x t h2)). Qed.
Lemma lem5977451 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5977452 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : (term593 A B op x t f) = (term594 A B x op t f).
Proof. exact (MK_COMB (@lem5977451 B) (@lem5977450 A B f op g x t h1 h2)). Qed.
Lemma lem5977565 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term533 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5976683 _120519 _120521 x op s f) (@lem5976676 _120519 _120521 x op s f)). Qed.
Lemma lem5977566 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term569 A B x op s f.
Proof. exact (@lem5977565 B A x op s f). Qed.
Lemma lem5977567 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term569 A B x op t g.
Proof. exact (@lem5977566 A B x op t g). Qed.
Lemma lem5977571 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem5976962 A t) (@lem5976961 A B f op g x t h1)). Qed.
Lemma lem5977572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5977573 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : (term570 A t) = (and True).
Proof. exact (MK_COMB (@lem5977572) (@lem5977571 A B f op g x t h1)). Qed.
Lemma lem5977575 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5976694 B op) (@lem5970116 B op h1)). Qed.
Lemma lem5977576 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : (term571 A B t op) = (True /\ True).
Proof. exact (MK_COMB (@lem5977573 A B f op g x t h2) (@lem5977575 B op h1)). Qed.
Lemma lem5977578 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5977579 : (True /\ True) = True.
Proof. exact (@lem5977578 True). Qed.
Lemma lem5977580 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : (term571 A B t op) = True.
Proof. exact (TRANS (@lem5977576 A B f op g x t h1 h2) (@lem5977579)). Qed.
Lemma lem5977581 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : True = (term571 A B t op).
Proof. exact (SYM (@lem5977580 A B f op g x t h1 h2)). Qed.
Lemma lem5977582 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : term571 A B t op.
Proof. exact (EQ_MP (@lem5977581 A B f op g x t h1 h2) (@lem0)). Qed.
Lemma lem5977583 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : (term562 A B op x t g) = (term572 A B x op t g).
Proof. exact (@lem5977567 A B x op t g (@lem5977582 A B f op g x t h1 h2)). Qed.
Lemma lem5977585 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term573 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5977586 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term574 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5977585 _2963 g t e g' t' e'). Qed.
Lemma lem5977587 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term575 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5977586 _2963 g t e g' t'). Qed.
Lemma lem5977588 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term576 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5977587 _2963 g t e g'). Qed.
Lemma lem5977589 {B : Type'} (g : Prop) (t : B) (e : B) : term576 B g t e.
Proof. exact (@lem5977588 B g t e). Qed.
Lemma lem5977590 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term577 A B x op t g.
Proof. exact (@lem5977589 B (@IN A x t) (@iterate B A op t g) (term578 A B x op t g)). Qed.
Lemma lem5977591 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) : term579 A B x op t g g'.
Proof. exact (@lem5977590 A B x op t g g'). Qed.
Lemma lem5977592 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) : (term579 A B x op t g g') = (term580 A B x op t g g').
Proof. exact (eq_refl (term579 A B x op t g g')). Qed.
Lemma lem5977593 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) : term580 A B x op t g g'.
Proof. exact (EQ_MP (@lem5977592 A B x op t g g') (@lem5977591 A B x op t g g')). Qed.
Lemma lem5977594 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) : term581 A B x op t g g' t'.
Proof. exact (@lem5977593 A B x op t g g' t'). Qed.
Lemma lem5977595 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) : (term581 A B x op t g g' t') = (term582 A B x op t g g' t').
Proof. exact (eq_refl (term581 A B x op t g g' t')). Qed.
Lemma lem5977596 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) : term582 A B x op t g g' t'.
Proof. exact (EQ_MP (@lem5977595 A B x op t g g' t') (@lem5977594 A B x op t g g' t')). Qed.
Lemma lem5977597 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) (e' : B) : term583 A B x op t g g' t' e'.
Proof. exact (@lem5977596 A B x op t g g' t' e'). Qed.
Lemma lem5977598 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) (e' : B) : (term583 A B x op t g g' t' e') = (term584 A B x op t g g' t' e').
Proof. exact (eq_refl (term583 A B x op t g g' t' e')). Qed.
Lemma lem5977599 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (g' : Prop) (t' : B) (e' : B) : term584 A B x op t g g' t' e'.
Proof. exact (EQ_MP (@lem5977598 A B x op t g g' t' e') (@lem5977597 A B x op t g g' t' e')). Qed.
Lemma lem5977601 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : (@IN A x t) = False.
Proof. exact (@lem5976965 A x t (@lem5976964 A B f op g x t h1)). Qed.
Lemma lem5977602 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (t' : B) (e' : B) : term585 A B x op t g t' e'.
Proof. exact (@lem5977599 A B x op t g False t' e'). Qed.
Lemma lem5977603 {A B : Type'} (t' : B) (e' : B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : term586 A B x op t g t' e'.
Proof. exact (@lem5977602 A B x op t g t' e' (@lem5977601 A B f op g x t h1)). Qed.
Lemma lem5977607 {A B : Type'} (op : type1400 B) (t : A -> Prop) (g : A -> B) : (@iterate B A op t g) = (@iterate B A op t g).
Proof. exact (eq_refl (@iterate B A op t g)). Qed.
Lemma lem5977608 {A B : Type'} (op : type1400 B) (t : A -> Prop) (g : A -> B) : term587 A B op t g.
Proof. exact (fun h0 : False => @lem5977607 A B op t g). Qed.
Lemma lem5977609 {A B : Type'} (e' : B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : term588 A B x op t g e'.
Proof. exact (@lem5977603 A B (@iterate B A op t g) e' f op g x t h1). Qed.
Lemma lem5977610 {A B : Type'} (e' : B) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : term589 A B x op t g e'.
Proof. exact (@lem5977609 A B e' f op g x t h1 (@lem5977608 A B op t g)). Qed.
Lemma lem5977616 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term578 A B x op t g) = (term578 A B x op t g).
Proof. exact (eq_refl (term578 A B x op t g)). Qed.
Lemma lem5977617 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term590 A B x op t g.
Proof. exact (fun h0 : ~ False => @lem5977616 A B x op t g). Qed.
Lemma lem5977618 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : term591 A B x op t g.
Proof. exact (@lem5977610 A B (term578 A B x op t g) f op g x t h1). Qed.
Lemma lem5977619 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : (term572 A B x op t g) = (term592 A B x op t g).
Proof. exact (@lem5977618 A B f op g x t h1 (@lem5977617 A B x op t g)). Qed.
Lemma lem5977621 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5977622 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5977621 B t1 t2). Qed.
Lemma lem5977623 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term592 A B x op t g) = (term578 A B x op t g).
Proof. exact (@lem5977622 B (@iterate B A op t g) (term578 A B x op t g)). Qed.
Lemma lem5977624 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : term492 A B f op g x t) : (term572 A B x op t g) = (term578 A B x op t g).
Proof. exact (TRANS (@lem5977619 A B f op g x t h1) (@lem5977623 A B x op t g)). Qed.
Lemma lem5977625 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : (term562 A B op x t g) = (term578 A B x op t g).
Proof. exact (TRANS (@lem5977583 A B f op g x t h1 h2) (@lem5977624 A B f op g x t h2)). Qed.
Lemma lem5977626 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : ((term562 A B op x t f) = (term562 A B op x t g)) = ((term578 A B x op t f) = (term578 A B x op t g)).
Proof. exact (MK_COMB (@lem5977452 A B f op g x t h1 h2) (@lem5977625 A B f op g x t h1 h2)). Qed.
Lemma lem5977740 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : term595 A B f x op t g.
Proof. exact (fun h0 : term561 A B x t f g => @lem5977626 A B f op g x t h1 h2). Qed.
Lemma lem5977741 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term596 A B f x op t g.
Proof. exact (@lem5977033 A B op x t f g ((term578 A B x op t f) = (term578 A B x op t g))). Qed.
Lemma lem5977742 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term492 A B f op g x t) : (term496 A B f op x t g) = (term597 A B f x op t g).
Proof. exact (@lem5977741 A B f x op t g (@lem5977740 A B f op g x t h1 h2)). Qed.
Lemma lem5978062 {A B : Type'} (f : A -> B) (x : A) (t : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term598 A B f x op t g.
Proof. exact (fun h0 : term492 A B f op g x t => @lem5977742 A B f op g x t h1 h0). Qed.
Lemma lem5978063 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term599 A B f x op t g.
Proof. exact (@lem5976958 A B f op g x t (term597 A B f x op t g)). Qed.
Lemma lem5978064 {A B : Type'} (f : A -> B) (x : A) (t : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term498 A B f op x t g) = (term600 A B f x op t g).
Proof. exact (@lem5978063 A B f x op t g (@lem5978062 A B f x t g op h1)). Qed.
Lemma lem5978799 {A B : Type'} (f : A -> B) (x : A) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term500 A B f op x g) = (term601 A B f x op g).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5978064 A B f x t g op h1)). Qed.
Lemma lem5979534 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5979535 {A B : Type'} (f : A -> B) (x : A) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term502 A B f op x g) = (term602 A B f x op g).
Proof. exact (MK_COMB (@lem5979534 A) (@lem5978799 A B f x g op h1)). Qed.
Lemma lem5980274 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term504 A B f op g) = (term603 A B f op g).
Proof. exact (fun_ext (fun x : A => @lem5979535 A B f x g op h1)). Qed.
Lemma lem5981013 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5981014 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term506 A B f op g) = (term604 A B f op g).
Proof. exact (MK_COMB (@lem5981013 A) (@lem5980274 A B f g op h1)). Qed.
Lemma lem5981757 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term508 A B f op g) = (term605 A B f op g).
Proof. exact (MK_COMB (@lem5976813 A B f g op h1) (@lem5981014 A B f g op h1)). Qed.
Lemma lem5981759 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5981760 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term605 A B f op g) = (term604 A B f op g).
Proof. exact (@lem5981759 (term604 A B f op g)). Qed.
Lemma lem5982503 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term508 A B f op g) = (term604 A B f op g).
Proof. exact (TRANS (@lem5981757 A B f g op h1) (@lem5981760 A B f op g)). Qed.
Lemma lem5982504 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term604 A B f op g) = (term508 A B f op g).
Proof. exact (SYM (@lem5982503 A B f g op h1)). Qed.
Lemma lem5982506 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5982507 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term604 A B f op g) = (term606 A B f op g).
Proof. exact (@lem5982506 (term604 A B f op g)). Qed.
Lemma lem5982508 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term606 A B f op g) = (term604 A B f op g).
Proof. exact (SYM (@lem5982507 A B f op g)). Qed.
Lemma lem5982509 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term607 A B f op g) : term607 A B f op g.
Proof. exact (h1). Qed.
Lemma lem5982510 {A : Type'} : term608 A.
Proof. exact (@lem3205665 A). Qed.
Lemma lem5982512 {B : Type'} : term608 B.
Proof. exact (@lem3205665 B). Qed.
Lemma lem5982515 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term609 A B f op g) : term609 A B f op g.
Proof. exact (h1). Qed.
Lemma lem5982516 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : term610 A B f op g.
Proof. exact (fun h0 : term609 A B f op g => @lem5982515 A B f op g h0). Qed.
Lemma lem5982517 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term610 A B f op g) : term610 A B f op g.
Proof. exact (h1). Qed.
Lemma lem5982518 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term609 A B f op g) : term609 A B f op g.
Proof. exact (h1). Qed.
Lemma lem5982519 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term609 A B f op g) (h2 : term610 A B f op g) : term609 A B f op g.
Proof. exact (@lem5982517 A B f op g h2 (@lem5982518 A B f op g h1)). Qed.
Lemma lem5982520 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term609 A B f op g) : term611 A B f op g.
Proof. exact (fun h0 : term610 A B f op g => @lem5982519 A B f op g h1 h0). Qed.
Lemma lem5982521 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term610 A B f op g) : term610 A B f op g.
Proof. exact (h1). Qed.
Lemma lem5982522 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term609 A B f op g) (h2 : term610 A B f op g) : term609 A B f op g.
Proof. exact (@lem5982520 A B f op g h1 (@lem5982521 A B f op g h2)). Qed.
Lemma lem5982523 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term610 A B f op g) : term610 A B f op g.
Proof. exact (fun h0 : term609 A B f op g => @lem5982522 A B f op g h0 h1). Qed.
Lemma lem5982524 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : term612 A B f op g.
Proof. exact (fun h0 : term610 A B f op g => @lem5982523 A B f op g h0). Qed.
Lemma lem5982527 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : term610 A B f op g.
Proof. exact (@lem5982524 A B f op g (@lem5982516 A B f op g)). Qed.
Lemma lem5982528 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : term610 A B f op g.
Proof. exact (@lem5982527 A B f op g). Qed.
Lemma lem5982590 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5982591 {B : Type'} : (term613 B) = (term614 B).
Proof. exact (@lem5982590 (term608 B)). Qed.
Lemma lem5982606 {A : Type'} : (term615 A) = (term615 A).
Proof. exact (eq_refl (term615 A)). Qed.
Lemma lem5982607 {A B : Type'} : (term616 A B) = (term617 A B).
Proof. exact (MK_COMB (@lem5982606 A) (@lem5982591 B)). Qed.
Lemma lem5982610 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term618 A B f op g) = (term618 A B f op g).
Proof. exact (eq_refl (term618 A B f op g)). Qed.
Lemma lem5982611 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term609 A B f op g) = (term619 A B f op g).
Proof. exact (MK_COMB (@lem5982610 A B f op g) (@lem5982607 A B)). Qed.
Lemma lem5982614 {A B : Type'} (op : type1400 B) (g : A -> B) : (term620 A B op g) = (term621 A B op g).
Proof. exact (fun_ext (fun f : A -> B => @lem5982611 A B f op g)). Qed.
Lemma lem5982615 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5982616 {A B : Type'} (op : type1400 B) (g : A -> B) : (term622 A B op g) = (term623 A B op g).
Proof. exact (MK_COMB (@lem5982615 A B) (@lem5982614 A B op g)). Qed.
Lemma lem5982621 {A B : Type'} (g : A -> B) : (term624 A B g) = (term625 A B g).
Proof. exact (fun_ext (fun op : type1400 B => @lem5982616 A B op g)). Qed.
Lemma lem5982622 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5982623 {A B : Type'} (g : A -> B) : (term626 A B g) = (term627 A B g).
Proof. exact (MK_COMB (@lem5982622 B) (@lem5982621 A B g)). Qed.
Lemma lem5982628 {A B : Type'} : (term628 A B) = (term629 A B).
Proof. exact (fun_ext (fun g : A -> B => @lem5982623 A B g)). Qed.
Lemma lem5982629 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5982638 {A B : Type'} : (term630 A B) = (term631 A B).
Proof. exact (MK_COMB (@lem5982629 A B) (@lem5982628 A B)). Qed.
Lemma lem5982647 {B : Type'} (y : B) (x : B) (s : B -> Prop) : ((term632 B x y s) = (term633 B y x s)) = ((term632 B x y s) = (term633 B y x s)).
Proof. exact (eq_refl ((term632 B x y s) = (term633 B y x s))). Qed.
Lemma lem5982648 {B : Type'} (y : B) (x : B) : (term634 B y x) = (term634 B y x).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5982647 B y x s)). Qed.
Lemma lem5982649 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5982650 {B : Type'} (y : B) (x : B) : (term635 B y x) = (term635 B y x).
Proof. exact (MK_COMB (@lem5982649 B) (@lem5982648 B y x)). Qed.
Lemma lem5982651 {B : Type'} (x : B) : (term636 B x) = (term636 B x).
Proof. exact (fun_ext (fun y : B => @lem5982650 B y x)). Qed.
Lemma lem5982652 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5982653 {B : Type'} (x : B) : (term637 B x) = (term637 B x).
Proof. exact (MK_COMB (@lem5982652 B) (@lem5982651 B x)). Qed.
Lemma lem5982654 {B : Type'} : (term638 B) = (term638 B).
Proof. exact (fun_ext (fun x : B => @lem5982653 B x)). Qed.
Lemma lem5982655 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5982656 {B : Type'} : (term608 B) = (term608 B).
Proof. exact (MK_COMB (@lem5982655 B) (@lem5982654 B)). Qed.
Lemma lem5982657 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5982658 {B : Type'} : (term614 B) = (term614 B).
Proof. exact (MK_COMB (@lem5982657) (@lem5982656 B)). Qed.
Lemma lem5982667 {A : Type'} (y : A) (x : A) (s : A -> Prop) : ((term632 A x y s) = (term633 A y x s)) = ((term632 A x y s) = (term633 A y x s)).
Proof. exact (eq_refl ((term632 A x y s) = (term633 A y x s))). Qed.
Lemma lem5982668 {A : Type'} (y : A) (x : A) : (term634 A y x) = (term634 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5982667 A y x s)). Qed.
Lemma lem5982669 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5982670 {A : Type'} (y : A) (x : A) : (term635 A y x) = (term635 A y x).
Proof. exact (MK_COMB (@lem5982669 A) (@lem5982668 A y x)). Qed.
Lemma lem5982671 {A : Type'} (x : A) : (term636 A x) = (term636 A x).
Proof. exact (fun_ext (fun y : A => @lem5982670 A y x)). Qed.
Lemma lem5982672 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5982673 {A : Type'} (x : A) : (term637 A x) = (term637 A x).
Proof. exact (MK_COMB (@lem5982672 A) (@lem5982671 A x)). Qed.
Lemma lem5982674 {A : Type'} : (term638 A) = (term638 A).
Proof. exact (fun_ext (fun x : A => @lem5982673 A x)). Qed.
Lemma lem5982675 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5982676 {A : Type'} : (term608 A) = (term608 A).
Proof. exact (MK_COMB (@lem5982675 A) (@lem5982674 A)). Qed.
Lemma lem5982677 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5982678 {A : Type'} : (term615 A) = (term615 A).
Proof. exact (MK_COMB (@lem5982677) (@lem5982676 A)). Qed.
Lemma lem5982679 {A B : Type'} : (term617 A B) = (term617 A B).
Proof. exact (MK_COMB (@lem5982678 A) (@lem5982658 B)). Qed.
Lemma lem5982680 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : ((term578 A B x op t f) = (term578 A B x op t g)) = ((term578 A B x op t f) = (term578 A B x op t g)).
Proof. exact (eq_refl ((term578 A B x op t f) = (term578 A B x op t g))). Qed.
Lemma lem5982685 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) : (term639 A B x t f g x') = (term639 A B x t f g x').
Proof. exact (eq_refl (term639 A B x t f g x')). Qed.
Lemma lem5982686 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term640 A B x t f g) = (term640 A B x t f g).
Proof. exact (fun_ext (fun x' : A => @lem5982685 A B x t f g x')). Qed.
Lemma lem5982687 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5982688 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term561 A B x t f g) = (term561 A B x t f g).
Proof. exact (MK_COMB (@lem5982687 A) (@lem5982686 A B x t f g)). Qed.
Lemma lem5982689 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5982690 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term641 A B x t f g) = (term641 A B x t f g).
Proof. exact (MK_COMB (@lem5982689) (@lem5982688 A B x t f g)). Qed.
Lemma lem5982691 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term597 A B f x op t g) = (term597 A B f x op t g).
Proof. exact (MK_COMB (@lem5982690 A B x t f g) (@lem5982680 A B f x op t g)). Qed.
Lemma lem5982698 {A : Type'} (x : A) (t : A -> Prop) : (term490 A x t) = (term490 A x t).
Proof. exact (eq_refl (term490 A x t)). Qed.
Lemma lem5982699 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : ((@iterate B A op t f) = (@iterate B A op t g)) = ((@iterate B A op t f) = (@iterate B A op t g)).
Proof. exact (eq_refl ((@iterate B A op t f) = (@iterate B A op t g))). Qed.
Lemma lem5982704 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term74 A B t f g x) = (term74 A B t f g x).
Proof. exact (eq_refl (term74 A B t f g x)). Qed.
Lemma lem5982705 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) : (term75 A B t f g) = (term75 A B t f g).
Proof. exact (fun_ext (fun x : A => @lem5982704 A B t f g x)). Qed.
Lemma lem5982706 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5982707 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) : (term26 A B t f g) = (term26 A B t f g).
Proof. exact (MK_COMB (@lem5982706 A) (@lem5982705 A B t f g)). Qed.
Lemma lem5982708 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5982709 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) : (term53 A B t f g) = (term53 A B t f g).
Proof. exact (MK_COMB (@lem5982708) (@lem5982707 A B t f g)). Qed.
Lemma lem5982710 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term487 A B f op t g) = (term487 A B f op t g).
Proof. exact (MK_COMB (@lem5982709 A B t f g) (@lem5982699 A B f op t g)). Qed.
Lemma lem5982711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5982712 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term489 A B f op t g) = (term489 A B f op t g).
Proof. exact (MK_COMB (@lem5982711) (@lem5982710 A B f op t g)). Qed.
Lemma lem5982713 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term492 A B f op g x t) = (term492 A B f op g x t).
Proof. exact (MK_COMB (@lem5982712 A B f op t g) (@lem5982698 A x t)). Qed.
Lemma lem5982714 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5982715 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term494 A B f op g x t) = (term494 A B f op g x t).
Proof. exact (MK_COMB (@lem5982714) (@lem5982713 A B f op g x t)). Qed.
Lemma lem5982716 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term600 A B f x op t g) = (term600 A B f x op t g).
Proof. exact (MK_COMB (@lem5982715 A B f op g x t) (@lem5982691 A B f x op t g)). Qed.
Lemma lem5982717 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) : (term601 A B f x op g) = (term601 A B f x op g).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5982716 A B f x op t g)). Qed.
Lemma lem5982718 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5982719 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) : (term602 A B f x op g) = (term602 A B f x op g).
Proof. exact (MK_COMB (@lem5982718 A) (@lem5982717 A B f x op g)). Qed.
Lemma lem5982720 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term603 A B f op g) = (term603 A B f op g).
Proof. exact (fun_ext (fun x : A => @lem5982719 A B f x op g)). Qed.
Lemma lem5982721 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5982722 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term604 A B f op g) = (term604 A B f op g).
Proof. exact (MK_COMB (@lem5982721 A) (@lem5982720 A B f op g)). Qed.
Lemma lem5982723 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5982724 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term607 A B f op g) = (term607 A B f op g).
Proof. exact (MK_COMB (@lem5982723) (@lem5982722 A B f op g)). Qed.
Lemma lem5982725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5982726 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term618 A B f op g) = (term618 A B f op g).
Proof. exact (MK_COMB (@lem5982725) (@lem5982724 A B f op g)). Qed.
Lemma lem5982727 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term619 A B f op g) = (term619 A B f op g).
Proof. exact (MK_COMB (@lem5982726 A B f op g) (@lem5982679 A B)). Qed.
Lemma lem5982728 {A B : Type'} (op : type1400 B) (g : A -> B) : (term621 A B op g) = (term621 A B op g).
Proof. exact (fun_ext (fun f : A -> B => @lem5982727 A B f op g)). Qed.
Lemma lem5982729 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5982730 {A B : Type'} (op : type1400 B) (g : A -> B) : (term623 A B op g) = (term623 A B op g).
Proof. exact (MK_COMB (@lem5982729 A B) (@lem5982728 A B op g)). Qed.
Lemma lem5982731 {A B : Type'} (g : A -> B) : (term625 A B g) = (term625 A B g).
Proof. exact (fun_ext (fun op : type1400 B => @lem5982730 A B op g)). Qed.
Lemma lem5982732 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5982733 {A B : Type'} (g : A -> B) : (term627 A B g) = (term627 A B g).
Proof. exact (MK_COMB (@lem5982732 B) (@lem5982731 A B g)). Qed.
Lemma lem5982734 {A B : Type'} : (term629 A B) = (term629 A B).
Proof. exact (fun_ext (fun g : A -> B => @lem5982733 A B g)). Qed.
Lemma lem5982735 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5982736 {A B : Type'} : (term631 A B) = (term631 A B).
Proof. exact (MK_COMB (@lem5982735 A B) (@lem5982734 A B)). Qed.
Lemma lem5982839 {A B : Type'} : (term630 A B) = (term631 A B).
Proof. exact (TRANS (@lem5982638 A B) (@lem5982736 A B)). Qed.
Lemma lem5982840 {A B : Type'} : (term631 A B) = (term630 A B).
Proof. exact (SYM (@lem5982839 A B)). Qed.
Lemma lem5982841 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term607 A B f op g) : term607 A B f op g.
Proof. exact (h1). Qed.
Lemma lem5982842 {A : Type'} (h1 : term608 A) : term608 A.
Proof. exact (h1). Qed.
Lemma lem5982850 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term642 A B t f g x) = (term643 A B t f g x).
Proof. exact (@lem17362 (@IN A x t) ((f x) = (g x))). Qed.
Lemma lem5982851 {A : Type'} (P : A -> Prop) : (term246 A P) = (term247 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5982852 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) : (term644 A B t f g) = (term645 A B t f g).
Proof. exact (@lem5982851 A (term75 A B t f g)). Qed.
Lemma lem5982853 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term646 A B t f g x) = (term74 A B t f g x).
Proof. exact (eq_refl (term646 A B t f g x)). Qed.
Lemma lem5982854 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5982855 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term647 A B t f g x) = (term642 A B t f g x).
Proof. exact (MK_COMB (@lem5982854) (@lem5982853 A B t f g x)). Qed.
Lemma lem5982856 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term647 A B t f g x) = (term643 A B t f g x).
Proof. exact (TRANS (@lem5982855 A B t f g x) (@lem5982850 A B t f g x)). Qed.
Lemma lem5982857 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) : (term648 A B t f g) = (term649 A B t f g).
Proof. exact (fun_ext (fun x : A => @lem5982856 A B t f g x)). Qed.
Lemma lem5982858 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5982859 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) : (term645 A B t f g) = (term650 A B t f g).
Proof. exact (MK_COMB (@lem5982858 A) (@lem5982857 A B t f g)). Qed.
Lemma lem5982860 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) : (term644 A B t f g) = (term650 A B t f g).
Proof. exact (TRANS (@lem5982852 A B t f g) (@lem5982859 A B t f g)). Qed.
Lemma lem5982861 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : ((@iterate B A op t f) = (@iterate B A op t g)) = ((@iterate B A op t f) = (@iterate B A op t g)).
Proof. exact (eq_refl ((@iterate B A op t f) = (@iterate B A op t g))). Qed.
Lemma lem5982862 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5982863 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) : (term651 A B t f g) = (term652 A B t f g).
Proof. exact (MK_COMB (@lem5982862) (@lem5982860 A B t f g)). Qed.
Lemma lem5982864 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term653 A B f op t g) = (term654 A B f op t g).
Proof. exact (MK_COMB (@lem5982863 A B t f g) (@lem5982861 A B f op t g)). Qed.
Lemma lem5982865 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term487 A B f op t g) = (term653 A B f op t g).
Proof. exact (@lem17265 (term26 A B t f g) ((@iterate B A op t f) = (@iterate B A op t g))). Qed.
Lemma lem5982866 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term487 A B f op t g) = (term654 A B f op t g).
Proof. exact (TRANS (@lem5982865 A B f op t g) (@lem5982864 A B f op t g)). Qed.
Lemma lem5982871 {A : Type'} (x : A) (t : A -> Prop) : (term490 A x t) = (term490 A x t).
Proof. exact (eq_refl (term490 A x t)). Qed.
Lemma lem5982872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5982873 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term489 A B f op t g) = (term655 A B f op t g).
Proof. exact (MK_COMB (@lem5982872) (@lem5982866 A B f op t g)). Qed.
Lemma lem5982874 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term492 A B f op g x t) = (term656 A B f op g x t).
Proof. exact (MK_COMB (@lem5982873 A B f op t g) (@lem5982871 A x t)). Qed.
Lemma lem5982881 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) : (term639 A B x t f g x') = (term657 A B x t f g x').
Proof. exact (@lem17265 (term632 A x' x t) ((f x') = (g x'))). Qed.
Lemma lem5982882 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term640 A B x t f g) = (term658 A B x t f g).
Proof. exact (fun_ext (fun x' : A => @lem5982881 A B x t f g x')). Qed.
Lemma lem5982883 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5982884 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term561 A B x t f g) = (term659 A B x t f g).
Proof. exact (MK_COMB (@lem5982883 A) (@lem5982882 A B x t f g)). Qed.
Lemma lem5982885 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term660 A B f x op t g) = (term660 A B f x op t g).
Proof. exact (eq_refl (term660 A B f x op t g)). Qed.
Lemma lem5982886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5982887 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term661 A B x t f g) = (term662 A B x t f g).
Proof. exact (MK_COMB (@lem5982886) (@lem5982884 A B x t f g)). Qed.
Lemma lem5982888 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term663 A B f x op t g) = (term664 A B f x op t g).
Proof. exact (MK_COMB (@lem5982887 A B x t f g) (@lem5982885 A B f x op t g)). Qed.
Lemma lem5982889 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term665 A B f x op t g) = (term663 A B f x op t g).
Proof. exact (@lem17362 (term561 A B x t f g) ((term578 A B x op t f) = (term578 A B x op t g))). Qed.
Lemma lem5982890 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term665 A B f x op t g) = (term664 A B f x op t g).
Proof. exact (TRANS (@lem5982889 A B f x op t g) (@lem5982888 A B f x op t g)). Qed.
Lemma lem5982891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5982892 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term666 A B f op g x t) = (term667 A B f op g x t).
Proof. exact (MK_COMB (@lem5982891) (@lem5982874 A B f op g x t)). Qed.
Lemma lem5982893 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term668 A B f x op t g) = (term669 A B f x op t g).
Proof. exact (MK_COMB (@lem5982892 A B f op g x t) (@lem5982890 A B f x op t g)). Qed.
Lemma lem5982894 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term670 A B f x op t g) = (term668 A B f x op t g).
Proof. exact (@lem17362 (term492 A B f op g x t) (term597 A B f x op t g)). Qed.
Lemma lem5982895 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term670 A B f x op t g) = (term669 A B f x op t g).
Proof. exact (TRANS (@lem5982894 A B f x op t g) (@lem5982893 A B f x op t g)). Qed.
Lemma lem5982896 {A : Type'} (P : type686 A) : (term671 A P) = (term672 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem5982897 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) : (term673 A B f x op g) = (term674 A B f x op g).
Proof. exact (@lem5982896 A (term601 A B f x op g)). Qed.
Lemma lem5982898 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term675 A B f x op g t) = (term600 A B f x op t g).
Proof. exact (eq_refl (term675 A B f x op g t)). Qed.
Lemma lem5982899 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5982900 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term676 A B f x op g t) = (term670 A B f x op t g).
Proof. exact (MK_COMB (@lem5982899) (@lem5982898 A B f x op t g)). Qed.
Lemma lem5982901 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term676 A B f x op g t) = (term669 A B f x op t g).
Proof. exact (TRANS (@lem5982900 A B f x op t g) (@lem5982895 A B f x op t g)). Qed.
Lemma lem5982902 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) : (term677 A B f x op g) = (term678 A B f x op g).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5982901 A B f x op t g)). Qed.
Lemma lem5982903 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5982904 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) : (term674 A B f x op g) = (term679 A B f x op g).
Proof. exact (MK_COMB (@lem5982903 A) (@lem5982902 A B f x op g)). Qed.
Lemma lem5982905 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) : (term673 A B f x op g) = (term679 A B f x op g).
Proof. exact (TRANS (@lem5982897 A B f x op g) (@lem5982904 A B f x op g)). Qed.
Lemma lem5982906 {A : Type'} (P : A -> Prop) : (term246 A P) = (term247 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5982907 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term607 A B f op g) = (term680 A B f op g).
Proof. exact (@lem5982906 A (term603 A B f op g)). Qed.
Lemma lem5982908 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) : (term681 A B f op g x) = (term602 A B f x op g).
Proof. exact (eq_refl (term681 A B f op g x)). Qed.
Lemma lem5982909 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5982910 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) : (term682 A B f op g x) = (term673 A B f x op g).
Proof. exact (MK_COMB (@lem5982909) (@lem5982908 A B f x op g)). Qed.
Lemma lem5982911 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) : (term682 A B f op g x) = (term679 A B f x op g).
Proof. exact (TRANS (@lem5982910 A B f x op g) (@lem5982905 A B f x op g)). Qed.
Lemma lem5982912 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term683 A B f op g) = (term684 A B f op g).
Proof. exact (fun_ext (fun x : A => @lem5982911 A B f x op g)). Qed.
Lemma lem5982913 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5982914 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term680 A B f op g) = (term685 A B f op g).
Proof. exact (MK_COMB (@lem5982913 A) (@lem5982912 A B f op g)). Qed.
Lemma lem5982915 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term607 A B f op g) = (term685 A B f op g).
Proof. exact (TRANS (@lem5982907 A B f op g) (@lem5982914 A B f op g)). Qed.
Lemma lem5983066 {A : Type'} (P : A -> Prop) (Q : Prop) : (term686 A P Q) = (term687 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5983067 {A : Type'} (P : A -> Prop) (Q : Prop) : (term686 A P Q) = (term687 A P Q).
Proof. exact (@lem5983066 A P Q). Qed.
Lemma lem5983068 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term688 A B f op t g) = (term689 A B f op t g).
Proof. exact (@lem5983067 A (term649 A B t f g) ((@iterate B A op t f) = (@iterate B A op t g))). Qed.
Lemma lem5983069 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term690 A B t f g x) = (term643 A B t f g x).
Proof. exact (eq_refl (term690 A B t f g x)). Qed.
Lemma lem5983070 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) : (term691 A B t f g) = (term649 A B t f g).
Proof. exact (fun_ext (fun x : A => @lem5983069 A B t f g x)). Qed.
Lemma lem5983071 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5983072 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) : (term692 A B t f g) = (term650 A B t f g).
Proof. exact (MK_COMB (@lem5983071 A) (@lem5983070 A B t f g)). Qed.
Lemma lem5983073 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5983074 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) : (term693 A B t f g) = (term652 A B t f g).
Proof. exact (MK_COMB (@lem5983073) (@lem5983072 A B t f g)). Qed.
Lemma lem5983075 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : ((@iterate B A op t f) = (@iterate B A op t g)) = ((@iterate B A op t f) = (@iterate B A op t g)).
Proof. exact (eq_refl ((@iterate B A op t f) = (@iterate B A op t g))). Qed.
Lemma lem5983076 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term688 A B f op t g) = (term654 A B f op t g).
Proof. exact (MK_COMB (@lem5983074 A B t f g) (@lem5983075 A B f op t g)). Qed.
Lemma lem5983077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5983078 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term694 A B f op t g) = (term695 A B f op t g).
Proof. exact (MK_COMB (@lem5983077) (@lem5983076 A B f op t g)). Qed.
Lemma lem5983079 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term690 A B t f g x) = (term643 A B t f g x).
Proof. exact (eq_refl (term690 A B t f g x)). Qed.
Lemma lem5983080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5983081 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term696 A B t f g x) = (term697 A B t f g x).
Proof. exact (MK_COMB (@lem5983080) (@lem5983079 A B t f g x)). Qed.
Lemma lem5983082 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : ((@iterate B A op t f) = (@iterate B A op t g)) = ((@iterate B A op t f) = (@iterate B A op t g)).
Proof. exact (eq_refl ((@iterate B A op t f) = (@iterate B A op t g))). Qed.
Lemma lem5983083 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term698 A B x f op t g) = (term699 A B x f op t g).
Proof. exact (MK_COMB (@lem5983081 A B t f g x) (@lem5983082 A B f op t g)). Qed.
Lemma lem5983084 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term700 A B f op t g) = (term701 A B f op t g).
Proof. exact (fun_ext (fun x : A => @lem5983083 A B x f op t g)). Qed.
Lemma lem5983085 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5983086 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term689 A B f op t g) = (term702 A B f op t g).
Proof. exact (MK_COMB (@lem5983085 A) (@lem5983084 A B f op t g)). Qed.
Lemma lem5983087 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : ((term688 A B f op t g) = (term689 A B f op t g)) = ((term654 A B f op t g) = (term702 A B f op t g)).
Proof. exact (MK_COMB (@lem5983078 A B f op t g) (@lem5983086 A B f op t g)). Qed.
Lemma lem5983088 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term654 A B f op t g) = (term702 A B f op t g).
Proof. exact (EQ_MP (@lem5983087 A B f op t g) (@lem5983068 A B f op t g)). Qed.
Lemma lem5983089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983090 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term655 A B f op t g) = (term703 A B f op t g).
Proof. exact (MK_COMB (@lem5983089) (@lem5983088 A B f op t g)). Qed.
Lemma lem5983091 {A : Type'} (x : A) (t : A -> Prop) : (term490 A x t) = (term490 A x t).
Proof. exact (eq_refl (term490 A x t)). Qed.
Lemma lem5983092 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term656 A B f op g x t) = (term704 A B f op g x t).
Proof. exact (MK_COMB (@lem5983090 A B f op t g) (@lem5983091 A x t)). Qed.
Lemma lem5983094 {A : Type'} (P : A -> Prop) (Q : Prop) : (term705 A P Q) = (term706 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5983095 {A : Type'} (P : A -> Prop) (Q : Prop) : (term705 A P Q) = (term706 A P Q).
Proof. exact (@lem5983094 A P Q). Qed.
Lemma lem5983096 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term707 A B f op g x t) = (term708 A B f op g x t).
Proof. exact (@lem5983095 A (term701 A B f op t g) (term490 A x t)). Qed.
Lemma lem5983097 {A B : Type'} (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term709 A B f op t g x) = (term699 A B x f op t g).
Proof. exact (eq_refl (term709 A B f op t g x)). Qed.
Lemma lem5983098 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term710 A B f op t g) = (term701 A B f op t g).
Proof. exact (fun_ext (fun x : A => @lem5983097 A B x f op t g)). Qed.
Lemma lem5983099 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5983100 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term711 A B f op t g) = (term702 A B f op t g).
Proof. exact (MK_COMB (@lem5983099 A) (@lem5983098 A B f op t g)). Qed.
Lemma lem5983101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983102 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term712 A B f op t g) = (term703 A B f op t g).
Proof. exact (MK_COMB (@lem5983101) (@lem5983100 A B f op t g)). Qed.
Lemma lem5983103 {A : Type'} (x : A) (t : A -> Prop) : (term490 A x t) = (term490 A x t).
Proof. exact (eq_refl (term490 A x t)). Qed.
Lemma lem5983104 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term707 A B f op g x t) = (term704 A B f op g x t).
Proof. exact (MK_COMB (@lem5983102 A B f op t g) (@lem5983103 A x t)). Qed.
Lemma lem5983105 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5983106 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term713 A B f op g x t) = (term714 A B f op g x t).
Proof. exact (MK_COMB (@lem5983105) (@lem5983104 A B f op g x t)). Qed.
Lemma lem5983107 {A B : Type'} (x' : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term709 A B f op t g x') = (term699 A B x' f op t g).
Proof. exact (eq_refl (term709 A B f op t g x')). Qed.
Lemma lem5983108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983109 {A B : Type'} (x' : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term715 A B f op t g x') = (term716 A B x' f op t g).
Proof. exact (MK_COMB (@lem5983108) (@lem5983107 A B x' f op t g)). Qed.
Lemma lem5983110 {A : Type'} (x : A) (t : A -> Prop) : (term490 A x t) = (term490 A x t).
Proof. exact (eq_refl (term490 A x t)). Qed.
Lemma lem5983111 {A B : Type'} (x' : A) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term717 A B f op g x' x t) = (term718 A B x' f op g x t).
Proof. exact (MK_COMB (@lem5983109 A B x' f op t g) (@lem5983110 A x t)). Qed.
Lemma lem5983112 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term719 A B f op g x t) = (term720 A B f op g x t).
Proof. exact (fun_ext (fun x' : A => @lem5983111 A B x' f op g x t)). Qed.
Lemma lem5983113 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5983114 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term708 A B f op g x t) = (term721 A B f op g x t).
Proof. exact (MK_COMB (@lem5983113 A) (@lem5983112 A B f op g x t)). Qed.
Lemma lem5983115 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : ((term707 A B f op g x t) = (term708 A B f op g x t)) = ((term704 A B f op g x t) = (term721 A B f op g x t)).
Proof. exact (MK_COMB (@lem5983106 A B f op g x t) (@lem5983114 A B f op g x t)). Qed.
Lemma lem5983116 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term704 A B f op g x t) = (term721 A B f op g x t).
Proof. exact (EQ_MP (@lem5983115 A B f op g x t) (@lem5983096 A B f op g x t)). Qed.
Lemma lem5983117 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term656 A B f op g x t) = (term721 A B f op g x t).
Proof. exact (TRANS (@lem5983092 A B f op g x t) (@lem5983116 A B f op g x t)). Qed.
Lemma lem5983118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983119 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term667 A B f op g x t) = (term722 A B f op g x t).
Proof. exact (MK_COMB (@lem5983118) (@lem5983117 A B f op g x t)). Qed.
Lemma lem5983120 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term664 A B f x op t g) = (term664 A B f x op t g).
Proof. exact (eq_refl (term664 A B f x op t g)). Qed.
Lemma lem5983121 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term669 A B f x op t g) = (term723 A B f x op t g).
Proof. exact (MK_COMB (@lem5983119 A B f op g x t) (@lem5983120 A B f x op t g)). Qed.
Lemma lem5983123 {A : Type'} (P : A -> Prop) (Q : Prop) : (term705 A P Q) = (term706 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5983124 {A : Type'} (P : A -> Prop) (Q : Prop) : (term705 A P Q) = (term706 A P Q).
Proof. exact (@lem5983123 A P Q). Qed.
Lemma lem5983125 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term724 A B f x op t g) = (term725 A B f x op t g).
Proof. exact (@lem5983124 A (term720 A B f op g x t) (term664 A B f x op t g)). Qed.
Lemma lem5983126 {A B : Type'} (x' : A) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term726 A B f op g x t x') = (term718 A B x' f op g x t).
Proof. exact (eq_refl (term726 A B f op g x t x')). Qed.
Lemma lem5983127 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term727 A B f op g x t) = (term720 A B f op g x t).
Proof. exact (fun_ext (fun x' : A => @lem5983126 A B x' f op g x t)). Qed.
Lemma lem5983128 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5983129 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term728 A B f op g x t) = (term721 A B f op g x t).
Proof. exact (MK_COMB (@lem5983128 A) (@lem5983127 A B f op g x t)). Qed.
Lemma lem5983130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983131 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term729 A B f op g x t) = (term722 A B f op g x t).
Proof. exact (MK_COMB (@lem5983130) (@lem5983129 A B f op g x t)). Qed.
Lemma lem5983132 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term664 A B f x op t g) = (term664 A B f x op t g).
Proof. exact (eq_refl (term664 A B f x op t g)). Qed.
Lemma lem5983133 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term724 A B f x op t g) = (term723 A B f x op t g).
Proof. exact (MK_COMB (@lem5983131 A B f op g x t) (@lem5983132 A B f x op t g)). Qed.
Lemma lem5983134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5983135 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term730 A B f x op t g) = (term731 A B f x op t g).
Proof. exact (MK_COMB (@lem5983134) (@lem5983133 A B f x op t g)). Qed.
Lemma lem5983136 {A B : Type'} (x' : A) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term726 A B f op g x t x') = (term718 A B x' f op g x t).
Proof. exact (eq_refl (term726 A B f op g x t x')). Qed.
Lemma lem5983137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983138 {A B : Type'} (x' : A) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term732 A B f op g x t x') = (term733 A B x' f op g x t).
Proof. exact (MK_COMB (@lem5983137) (@lem5983136 A B x' f op g x t)). Qed.
Lemma lem5983139 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term664 A B f x op t g) = (term664 A B f x op t g).
Proof. exact (eq_refl (term664 A B f x op t g)). Qed.
Lemma lem5983140 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term734 A B x' f x op t g) = (term735 A B x' f x op t g).
Proof. exact (MK_COMB (@lem5983138 A B x' f op g x t) (@lem5983139 A B f x op t g)). Qed.
Lemma lem5983141 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term736 A B f x op t g) = (term737 A B f x op t g).
Proof. exact (fun_ext (fun x' : A => @lem5983140 A B x' f x op t g)). Qed.
Lemma lem5983142 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5983143 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term725 A B f x op t g) = (term738 A B f x op t g).
Proof. exact (MK_COMB (@lem5983142 A) (@lem5983141 A B f x op t g)). Qed.
Lemma lem5983144 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : ((term724 A B f x op t g) = (term725 A B f x op t g)) = ((term723 A B f x op t g) = (term738 A B f x op t g)).
Proof. exact (MK_COMB (@lem5983135 A B f x op t g) (@lem5983143 A B f x op t g)). Qed.
Lemma lem5983145 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term723 A B f x op t g) = (term738 A B f x op t g).
Proof. exact (EQ_MP (@lem5983144 A B f x op t g) (@lem5983125 A B f x op t g)). Qed.
Lemma lem5983146 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term669 A B f x op t g) = (term738 A B f x op t g).
Proof. exact (TRANS (@lem5983121 A B f x op t g) (@lem5983145 A B f x op t g)). Qed.
Lemma lem5983147 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) : (term678 A B f x op g) = (term739 A B f x op g).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5983146 A B f x op t g)). Qed.
Lemma lem5983148 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5983149 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) : (term679 A B f x op g) = (term740 A B f x op g).
Proof. exact (MK_COMB (@lem5983148 A) (@lem5983147 A B f x op g)). Qed.
Lemma lem5983150 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term684 A B f op g) = (term741 A B f op g).
Proof. exact (fun_ext (fun x : A => @lem5983149 A B f x op g)). Qed.
Lemma lem5983151 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5983153 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term685 A B f op g) = (term742 A B f op g).
Proof. exact (MK_COMB (@lem5983151 A) (@lem5983150 A B f op g)). Qed.
Lemma lem5983154 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term607 A B f op g) = (term742 A B f op g).
Proof. exact (TRANS (@lem5982915 A B f op g) (@lem5983153 A B f op g)). Qed.
Lemma lem5983155 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term607 A B f op g) : term742 A B f op g.
Proof. exact (EQ_MP (@lem5983154 A B f op g) (@lem5982841 A B f op g h1)). Qed.
Lemma lem5983166 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term743 A y x s) = (term744 A y x s).
Proof. exact (@lem17160 (x = y) (@IN A x s)). Qed.
Lemma lem5983172 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term745 A y x s) = (term745 A y x s).
Proof. exact (eq_refl (term745 A y x s)). Qed.
Lemma lem5983174 {A : Type'} (x : A) (y : A) (s : A -> Prop) : (term746 A x y s) = (term746 A x y s).
Proof. exact (eq_refl (term746 A x y s)). Qed.
Lemma lem5983175 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term747 A y x s) = (term748 A y x s).
Proof. exact (MK_COMB (@lem5983174 A x y s) (@lem5983166 A y x s)). Qed.
Lemma lem5983176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983177 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term749 A y x s) = (term750 A y x s).
Proof. exact (MK_COMB (@lem5983176) (@lem5983175 A y x s)). Qed.
Lemma lem5983178 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term751 A y x s) = (term752 A y x s).
Proof. exact (MK_COMB (@lem5983177 A y x s) (@lem5983172 A y x s)). Qed.
Lemma lem5983179 {A : Type'} (y : A) (x : A) (s : A -> Prop) : ((term632 A x y s) = (term633 A y x s)) = (term751 A y x s).
Proof. exact (@lem17784 (term632 A x y s) (term633 A y x s)). Qed.
Lemma lem5983180 {A : Type'} (y : A) (x : A) (s : A -> Prop) : ((term632 A x y s) = (term633 A y x s)) = (term752 A y x s).
Proof. exact (TRANS (@lem5983179 A y x s) (@lem5983178 A y x s)). Qed.
Lemma lem5983181 {A : Type'} (y : A) (x : A) : (term634 A y x) = (term753 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5983180 A y x s)). Qed.
Lemma lem5983182 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5983183 {A : Type'} (y : A) (x : A) : (term635 A y x) = (term754 A y x).
Proof. exact (MK_COMB (@lem5983182 A) (@lem5983181 A y x)). Qed.
Lemma lem5983184 {A : Type'} (x : A) : (term636 A x) = (term755 A x).
Proof. exact (fun_ext (fun y : A => @lem5983183 A y x)). Qed.
Lemma lem5983185 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5983186 {A : Type'} (x : A) : (term637 A x) = (term756 A x).
Proof. exact (MK_COMB (@lem5983185 A) (@lem5983184 A x)). Qed.
Lemma lem5983187 {A : Type'} : (term638 A) = (term757 A).
Proof. exact (fun_ext (fun x : A => @lem5983186 A x)). Qed.
Lemma lem5983188 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5983189 {A : Type'} : (term608 A) = (term758 A).
Proof. exact (MK_COMB (@lem5983188 A) (@lem5983187 A)). Qed.
Lemma lem5983199 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term288 A P Q) = (term289 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5983200 {A : Type'} (P : type686 A) (Q : type686 A) : (term290 A P Q) = (term291 A P Q).
Proof. exact (@lem5983199 (A -> Prop) P Q). Qed.
Lemma lem5983201 {A : Type'} (y : A) (x : A) : (term759 A y x) = (term760 A y x).
Proof. exact (@lem5983200 A (term761 A y x) (term762 A y x)). Qed.
Lemma lem5983202 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term763 A y x s) = (term748 A y x s).
Proof. exact (eq_refl (term763 A y x s)). Qed.
Lemma lem5983203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983204 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term764 A y x s) = (term750 A y x s).
Proof. exact (MK_COMB (@lem5983203) (@lem5983202 A y x s)). Qed.
Lemma lem5983205 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term765 A y x s) = (term745 A y x s).
Proof. exact (eq_refl (term765 A y x s)). Qed.
Lemma lem5983206 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term766 A y x s) = (term752 A y x s).
Proof. exact (MK_COMB (@lem5983204 A y x s) (@lem5983205 A y x s)). Qed.
Lemma lem5983207 {A : Type'} (y : A) (x : A) : (term767 A y x) = (term753 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5983206 A y x s)). Qed.
Lemma lem5983208 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5983209 {A : Type'} (y : A) (x : A) : (term759 A y x) = (term754 A y x).
Proof. exact (MK_COMB (@lem5983208 A) (@lem5983207 A y x)). Qed.
Lemma lem5983210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5983211 {A : Type'} (y : A) (x : A) : (term768 A y x) = (term769 A y x).
Proof. exact (MK_COMB (@lem5983210) (@lem5983209 A y x)). Qed.
Lemma lem5983212 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term763 A y x s) = (term748 A y x s).
Proof. exact (eq_refl (term763 A y x s)). Qed.
Lemma lem5983213 {A : Type'} (y : A) (x : A) : (term770 A y x) = (term761 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5983212 A y x s)). Qed.
Lemma lem5983214 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5983215 {A : Type'} (y : A) (x : A) : (term771 A y x) = (term772 A y x).
Proof. exact (MK_COMB (@lem5983214 A) (@lem5983213 A y x)). Qed.
Lemma lem5983216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983217 {A : Type'} (y : A) (x : A) : (term773 A y x) = (term774 A y x).
Proof. exact (MK_COMB (@lem5983216) (@lem5983215 A y x)). Qed.
Lemma lem5983218 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term765 A y x s) = (term745 A y x s).
Proof. exact (eq_refl (term765 A y x s)). Qed.
Lemma lem5983219 {A : Type'} (y : A) (x : A) : (term775 A y x) = (term762 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5983218 A y x s)). Qed.
Lemma lem5983220 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5983221 {A : Type'} (y : A) (x : A) : (term776 A y x) = (term777 A y x).
Proof. exact (MK_COMB (@lem5983220 A) (@lem5983219 A y x)). Qed.
Lemma lem5983222 {A : Type'} (y : A) (x : A) : (term760 A y x) = (term778 A y x).
Proof. exact (MK_COMB (@lem5983217 A y x) (@lem5983221 A y x)). Qed.
Lemma lem5983223 {A : Type'} (y : A) (x : A) : ((term759 A y x) = (term760 A y x)) = ((term754 A y x) = (term778 A y x)).
Proof. exact (MK_COMB (@lem5983211 A y x) (@lem5983222 A y x)). Qed.
Lemma lem5983224 {A : Type'} (y : A) (x : A) : (term754 A y x) = (term778 A y x).
Proof. exact (EQ_MP (@lem5983223 A y x) (@lem5983201 A y x)). Qed.
Lemma lem5983321 {A : Type'} (x : A) : (term755 A x) = (term779 A x).
Proof. exact (fun_ext (fun y : A => @lem5983224 A y x)). Qed.
Lemma lem5983322 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5983323 {A : Type'} (x : A) : (term756 A x) = (term780 A x).
Proof. exact (MK_COMB (@lem5983322 A) (@lem5983321 A x)). Qed.
Lemma lem5983325 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term288 A P Q) = (term289 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5983326 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term288 A P Q) = (term289 A P Q).
Proof. exact (@lem5983325 A P Q). Qed.
Lemma lem5983327 {A : Type'} (x : A) : (term781 A x) = (term782 A x).
Proof. exact (@lem5983326 A (term783 A x) (term784 A x)). Qed.
Lemma lem5983328 {A : Type'} (y : A) (x : A) : (term785 A x y) = (term772 A y x).
Proof. exact (eq_refl (term785 A x y)). Qed.
Lemma lem5983329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983330 {A : Type'} (y : A) (x : A) : (term786 A x y) = (term774 A y x).
Proof. exact (MK_COMB (@lem5983329) (@lem5983328 A y x)). Qed.
Lemma lem5983331 {A : Type'} (y : A) (x : A) : (term787 A x y) = (term777 A y x).
Proof. exact (eq_refl (term787 A x y)). Qed.
Lemma lem5983332 {A : Type'} (y : A) (x : A) : (term788 A x y) = (term778 A y x).
Proof. exact (MK_COMB (@lem5983330 A y x) (@lem5983331 A y x)). Qed.
Lemma lem5983333 {A : Type'} (x : A) : (term789 A x) = (term779 A x).
Proof. exact (fun_ext (fun y : A => @lem5983332 A y x)). Qed.
Lemma lem5983334 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5983335 {A : Type'} (x : A) : (term781 A x) = (term780 A x).
Proof. exact (MK_COMB (@lem5983334 A) (@lem5983333 A x)). Qed.
Lemma lem5983336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5983337 {A : Type'} (x : A) : (term790 A x) = (term791 A x).
Proof. exact (MK_COMB (@lem5983336) (@lem5983335 A x)). Qed.
Lemma lem5983338 {A : Type'} (y : A) (x : A) : (term785 A x y) = (term772 A y x).
Proof. exact (eq_refl (term785 A x y)). Qed.
Lemma lem5983339 {A : Type'} (x : A) : (term792 A x) = (term783 A x).
Proof. exact (fun_ext (fun y : A => @lem5983338 A y x)). Qed.
Lemma lem5983340 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5983341 {A : Type'} (x : A) : (term793 A x) = (term794 A x).
Proof. exact (MK_COMB (@lem5983340 A) (@lem5983339 A x)). Qed.
Lemma lem5983342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983343 {A : Type'} (x : A) : (term795 A x) = (term796 A x).
Proof. exact (MK_COMB (@lem5983342) (@lem5983341 A x)). Qed.
Lemma lem5983344 {A : Type'} (y : A) (x : A) : (term787 A x y) = (term777 A y x).
Proof. exact (eq_refl (term787 A x y)). Qed.
Lemma lem5983345 {A : Type'} (x : A) : (term797 A x) = (term784 A x).
Proof. exact (fun_ext (fun y : A => @lem5983344 A y x)). Qed.
Lemma lem5983346 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5983347 {A : Type'} (x : A) : (term798 A x) = (term799 A x).
Proof. exact (MK_COMB (@lem5983346 A) (@lem5983345 A x)). Qed.
Lemma lem5983348 {A : Type'} (x : A) : (term782 A x) = (term800 A x).
Proof. exact (MK_COMB (@lem5983343 A x) (@lem5983347 A x)). Qed.
Lemma lem5983349 {A : Type'} (x : A) : ((term781 A x) = (term782 A x)) = ((term780 A x) = (term800 A x)).
Proof. exact (MK_COMB (@lem5983337 A x) (@lem5983348 A x)). Qed.
Lemma lem5983350 {A : Type'} (x : A) : (term780 A x) = (term800 A x).
Proof. exact (EQ_MP (@lem5983349 A x) (@lem5983327 A x)). Qed.
Lemma lem5983455 {A : Type'} (x : A) : (term756 A x) = (term800 A x).
Proof. exact (TRANS (@lem5983323 A x) (@lem5983350 A x)). Qed.
Lemma lem5983456 {A : Type'} : (term757 A) = (term801 A).
Proof. exact (fun_ext (fun x : A => @lem5983455 A x)). Qed.
Lemma lem5983457 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5983458 {A : Type'} : (term758 A) = (term802 A).
Proof. exact (MK_COMB (@lem5983457 A) (@lem5983456 A)). Qed.
Lemma lem5983460 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term288 A P Q) = (term289 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5983461 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term288 A P Q) = (term289 A P Q).
Proof. exact (@lem5983460 A P Q). Qed.
Lemma lem5983462 {A : Type'} : (term803 A) = (term804 A).
Proof. exact (@lem5983461 A (term805 A) (term806 A)). Qed.
Lemma lem5983463 {A : Type'} (x : A) : (term807 A x) = (term794 A x).
Proof. exact (eq_refl (term807 A x)). Qed.
Lemma lem5983464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983465 {A : Type'} (x : A) : (term808 A x) = (term796 A x).
Proof. exact (MK_COMB (@lem5983464) (@lem5983463 A x)). Qed.
Lemma lem5983466 {A : Type'} (x : A) : (term809 A x) = (term799 A x).
Proof. exact (eq_refl (term809 A x)). Qed.
Lemma lem5983467 {A : Type'} (x : A) : (term810 A x) = (term800 A x).
Proof. exact (MK_COMB (@lem5983465 A x) (@lem5983466 A x)). Qed.
Lemma lem5983468 {A : Type'} : (term811 A) = (term801 A).
Proof. exact (fun_ext (fun x : A => @lem5983467 A x)). Qed.
Lemma lem5983469 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5983470 {A : Type'} : (term803 A) = (term802 A).
Proof. exact (MK_COMB (@lem5983469 A) (@lem5983468 A)). Qed.
Lemma lem5983471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5983472 {A : Type'} : (term812 A) = (term813 A).
Proof. exact (MK_COMB (@lem5983471) (@lem5983470 A)). Qed.
Lemma lem5983473 {A : Type'} (x : A) : (term807 A x) = (term794 A x).
Proof. exact (eq_refl (term807 A x)). Qed.
Lemma lem5983474 {A : Type'} : (term814 A) = (term805 A).
Proof. exact (fun_ext (fun x : A => @lem5983473 A x)). Qed.
Lemma lem5983475 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5983476 {A : Type'} : (term815 A) = (term816 A).
Proof. exact (MK_COMB (@lem5983475 A) (@lem5983474 A)). Qed.
Lemma lem5983477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5983478 {A : Type'} : (term817 A) = (term818 A).
Proof. exact (MK_COMB (@lem5983477) (@lem5983476 A)). Qed.
Lemma lem5983479 {A : Type'} (x : A) : (term809 A x) = (term799 A x).
Proof. exact (eq_refl (term809 A x)). Qed.
Lemma lem5983480 {A : Type'} : (term819 A) = (term806 A).
Proof. exact (fun_ext (fun x : A => @lem5983479 A x)). Qed.
Lemma lem5983481 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5983482 {A : Type'} : (term820 A) = (term821 A).
Proof. exact (MK_COMB (@lem5983481 A) (@lem5983480 A)). Qed.
Lemma lem5983483 {A : Type'} : (term804 A) = (term822 A).
Proof. exact (MK_COMB (@lem5983478 A) (@lem5983482 A)). Qed.
Lemma lem5983484 {A : Type'} : ((term803 A) = (term804 A)) = ((term802 A) = (term822 A)).
Proof. exact (MK_COMB (@lem5983472 A) (@lem5983483 A)). Qed.
Lemma lem5983485 {A : Type'} : (term802 A) = (term822 A).
Proof. exact (EQ_MP (@lem5983484 A) (@lem5983462 A)). Qed.
Lemma lem5983600 {A : Type'} : (term758 A) = (term822 A).
Proof. exact (TRANS (@lem5983458 A) (@lem5983485 A)). Qed.
Lemma lem5983601 {A : Type'} : (term608 A) = (term822 A).
Proof. exact (TRANS (@lem5983189 A) (@lem5983600 A)). Qed.
Lemma lem5983602 {A : Type'} (h1 : term608 A) : term822 A.
Proof. exact (EQ_MP (@lem5983601 A) (@lem5982842 A h1)). Qed.
Lemma lem5984050 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) (h1 : term740 A B f x op g) : term740 A B f x op g.
Proof. exact (h1). Qed.
Lemma lem5984051 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term738 A B f x op t g) : term738 A B f x op t g.
Proof. exact (h1). Qed.
Lemma lem5984052 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term735 A B x' f x op t g.
Proof. exact (h1). Qed.
Lemma lem5984079 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term745 A y x s) = (term745 A y x s).
Proof. exact (eq_refl (term745 A y x s)). Qed.
Lemma lem5984080 {A : Type'} (y : A) (x : A) : (term762 A y x) = (term762 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5984079 A y x s)). Qed.
Lemma lem5984081 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5984082 {A : Type'} (y : A) (x : A) : (term777 A y x) = (term777 A y x).
Proof. exact (MK_COMB (@lem5984081 A) (@lem5984080 A y x)). Qed.
Lemma lem5984083 {A : Type'} (x : A) : (term784 A x) = (term784 A x).
Proof. exact (fun_ext (fun y : A => @lem5984082 A y x)). Qed.
Lemma lem5984084 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5984085 {A : Type'} (x : A) : (term799 A x) = (term799 A x).
Proof. exact (MK_COMB (@lem5984084 A) (@lem5984083 A x)). Qed.
Lemma lem5984086 {A : Type'} : (term806 A) = (term806 A).
Proof. exact (fun_ext (fun x : A => @lem5984085 A x)). Qed.
Lemma lem5984087 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5984088 {A : Type'} : (term821 A) = (term821 A).
Proof. exact (MK_COMB (@lem5984087 A) (@lem5984086 A)). Qed.
Lemma lem5984117 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term748 A y x s) = (term748 A y x s).
Proof. exact (eq_refl (term748 A y x s)). Qed.
Lemma lem5984118 {A : Type'} (y : A) (x : A) : (term761 A y x) = (term761 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5984117 A y x s)). Qed.
Lemma lem5984119 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5984120 {A : Type'} (y : A) (x : A) : (term772 A y x) = (term772 A y x).
Proof. exact (MK_COMB (@lem5984119 A) (@lem5984118 A y x)). Qed.
Lemma lem5984121 {A : Type'} (x : A) : (term783 A x) = (term783 A x).
Proof. exact (fun_ext (fun y : A => @lem5984120 A y x)). Qed.
Lemma lem5984122 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5984123 {A : Type'} (x : A) : (term794 A x) = (term794 A x).
Proof. exact (MK_COMB (@lem5984122 A) (@lem5984121 A x)). Qed.
Lemma lem5984124 {A : Type'} : (term805 A) = (term805 A).
Proof. exact (fun_ext (fun x : A => @lem5984123 A x)). Qed.
Lemma lem5984125 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5984126 {A : Type'} : (term816 A) = (term816 A).
Proof. exact (MK_COMB (@lem5984125 A) (@lem5984124 A)). Qed.
Lemma lem5984127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5984128 {A : Type'} : (term818 A) = (term818 A).
Proof. exact (MK_COMB (@lem5984127) (@lem5984126 A)). Qed.
Lemma lem5984129 {A : Type'} : (term822 A) = (term822 A).
Proof. exact (MK_COMB (@lem5984128 A) (@lem5984088 A)). Qed.
Lemma lem5984130 {A : Type'} (h1 : term608 A) : term822 A.
Proof. exact (EQ_MP (@lem5984129 A) (@lem5983602 A h1)). Qed.
Lemma lem5984209 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5984210 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5984211 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5984216 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5984218 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5984216 A B f x). Qed.
Lemma lem5984225 {A B : Type'} (op : type1400 B) (t : A -> Prop) (f : A -> B) : (@iterate B A op t f) = (@iterate B A op t f).
Proof. exact (eq_refl (@iterate B A op t f)). Qed.
Lemma lem5984226 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term823 A B op f x) = (term824 A B op f x).
Proof. exact (MK_COMB (@lem5984211 B op) (@lem5984218 A B f x)). Qed.
Lemma lem5984227 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term578 A B x op t f) = (term825 A B x op t f).
Proof. exact (MK_COMB (@lem5984226 A B op f x) (@lem5984225 A B op t f)). Qed.
Lemma lem5984229 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5984230 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5984229 B (B -> B) f x). Qed.
Lemma lem5984231 {A B : Type'} (op : type1400 B) (f : A -> B) (x : A) : (term824 A B op f x) = (term826 A B op f x).
Proof. exact (@lem5984230 B op (@I (A -> B) f x)). Qed.
Lemma lem5984232 {A B : Type'} (op : type1400 B) (t : A -> Prop) (f : A -> B) : (@iterate B A op t f) = (@iterate B A op t f).
Proof. exact (eq_refl (@iterate B A op t f)). Qed.
Lemma lem5984233 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term825 A B x op t f) = (term827 A B x op t f).
Proof. exact (MK_COMB (@lem5984231 A B op f x) (@lem5984232 A B op t f)). Qed.
Lemma lem5984235 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5984236 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5984235 B B f x). Qed.
Lemma lem5984237 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term827 A B x op t f) = (term828 A B x op t f).
Proof. exact (@lem5984236 B (term826 A B op f x) (@iterate B A op t f)). Qed.
Lemma lem5984238 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term825 A B x op t f) = (term828 A B x op t f).
Proof. exact (TRANS (@lem5984233 A B x op t f) (@lem5984237 A B x op t f)). Qed.
Lemma lem5984239 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term578 A B x op t f) = (term828 A B x op t f).
Proof. exact (TRANS (@lem5984227 A B x op t f) (@lem5984238 A B x op t f)). Qed.
Lemma lem5984240 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5984245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5984246 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5984245 A B f x). Qed.
Lemma lem5984248 {A B : Type'} (g : A -> B) (x : A) : (g x) = (@I (A -> B) g x).
Proof. exact (@lem5984246 A B g x). Qed.
Lemma lem5984255 {A B : Type'} (op : type1400 B) (t : A -> Prop) (g : A -> B) : (@iterate B A op t g) = (@iterate B A op t g).
Proof. exact (eq_refl (@iterate B A op t g)). Qed.
Lemma lem5984256 {A B : Type'} (op : type1400 B) (g : A -> B) (x : A) : (term823 A B op g x) = (term824 A B op g x).
Proof. exact (MK_COMB (@lem5984240 B op) (@lem5984248 A B g x)). Qed.
Lemma lem5984257 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term578 A B x op t g) = (term825 A B x op t g).
Proof. exact (MK_COMB (@lem5984256 A B op g x) (@lem5984255 A B op t g)). Qed.
Lemma lem5984259 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5984260 {B : Type'} (f : type1400 B) (x : B) : (f x) = (@I (B -> B -> B) f x).
Proof. exact (@lem5984259 B (B -> B) f x). Qed.
Lemma lem5984261 {A B : Type'} (op : type1400 B) (g : A -> B) (x : A) : (term824 A B op g x) = (term826 A B op g x).
Proof. exact (@lem5984260 B op (@I (A -> B) g x)). Qed.
Lemma lem5984262 {A B : Type'} (op : type1400 B) (t : A -> Prop) (g : A -> B) : (@iterate B A op t g) = (@iterate B A op t g).
Proof. exact (eq_refl (@iterate B A op t g)). Qed.
Lemma lem5984263 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term825 A B x op t g) = (term827 A B x op t g).
Proof. exact (MK_COMB (@lem5984261 A B op g x) (@lem5984262 A B op t g)). Qed.
Lemma lem5984265 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5984266 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem5984265 B B f x). Qed.
Lemma lem5984267 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term827 A B x op t g) = (term828 A B x op t g).
Proof. exact (@lem5984266 B (term826 A B op g x) (@iterate B A op t g)). Qed.
Lemma lem5984268 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term825 A B x op t g) = (term828 A B x op t g).
Proof. exact (TRANS (@lem5984263 A B x op t g) (@lem5984267 A B x op t g)). Qed.
Lemma lem5984269 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term578 A B x op t g) = (term828 A B x op t g).
Proof. exact (TRANS (@lem5984257 A B x op t g) (@lem5984268 A B x op t g)). Qed.
Lemma lem5984270 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term594 A B x op t f) = (term829 A B x op t f).
Proof. exact (MK_COMB (@lem5984210 B) (@lem5984239 A B x op t f)). Qed.
Lemma lem5984271 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : ((term578 A B x op t f) = (term578 A B x op t g)) = ((term828 A B x op t f) = (term828 A B x op t g)).
Proof. exact (MK_COMB (@lem5984270 A B x op t f) (@lem5984269 A B x op t g)). Qed.
Lemma lem5984272 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term660 A B f x op t g) = (term830 A B f x op t g).
Proof. exact (MK_COMB (@lem5984209) (@lem5984271 A B f x op t g)). Qed.
Lemma lem5984273 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5984278 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5984279 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5984278 A B f x). Qed.
Lemma lem5984281 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem5984279 A B f x'). Qed.
Lemma lem5984286 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5984287 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5984286 A B f x). Qed.
Lemma lem5984289 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem5984287 A B g x'). Qed.
Lemma lem5984290 {A B : Type'} (f : A -> B) (x' : A) : (term382 A B f x') = (term383 A B f x').
Proof. exact (MK_COMB (@lem5984273 B) (@lem5984281 A B f x')). Qed.
Lemma lem5984291 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) : ((f x') = (g x')) = ((@I (A -> B) f x') = (@I (A -> B) g x')).
Proof. exact (MK_COMB (@lem5984290 A B f x') (@lem5984289 A B g x')). Qed.
Lemma lem5984304 {A : Type'} (x' : A) (x : A) (t : A -> Prop) : (term831 A x' x t) = (term831 A x' x t).
Proof. exact (eq_refl (term831 A x' x t)). Qed.
Lemma lem5984305 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) : (term657 A B x t f g x') = (term832 A B x t f g x').
Proof. exact (MK_COMB (@lem5984304 A x' x t) (@lem5984291 A B f g x')). Qed.
Lemma lem5984306 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term658 A B x t f g) = (term833 A B x t f g).
Proof. exact (fun_ext (fun x' : A => @lem5984305 A B x t f g x')). Qed.
Lemma lem5984307 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5984308 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term659 A B x t f g) = (term834 A B x t f g).
Proof. exact (MK_COMB (@lem5984307 A) (@lem5984306 A B x t f g)). Qed.
Lemma lem5984309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5984310 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term662 A B x t f g) = (term835 A B x t f g).
Proof. exact (MK_COMB (@lem5984309) (@lem5984308 A B x t f g)). Qed.
Lemma lem5984311 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term664 A B f x op t g) = (term836 A B f x op t g).
Proof. exact (MK_COMB (@lem5984310 A B x t f g) (@lem5984272 A B f x op t g)). Qed.
Lemma lem5984324 {A : Type'} (x : A) (t : A -> Prop) : (term490 A x t) = (term490 A x t).
Proof. exact (eq_refl (term490 A x t)). Qed.
Lemma lem5984341 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : ((@iterate B A op t f) = (@iterate B A op t g)) = ((@iterate B A op t f) = (@iterate B A op t g)).
Proof. exact (eq_refl ((@iterate B A op t f) = (@iterate B A op t g))). Qed.
Lemma lem5984342 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5984343 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5984348 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5984349 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5984348 A B f x). Qed.
Lemma lem5984351 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (@I (A -> B) f x').
Proof. exact (@lem5984349 A B f x'). Qed.
Lemma lem5984356 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5984357 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem5984356 A B f x). Qed.
Lemma lem5984359 {A B : Type'} (g : A -> B) (x' : A) : (g x') = (@I (A -> B) g x').
Proof. exact (@lem5984357 A B g x'). Qed.
Lemma lem5984360 {A B : Type'} (f : A -> B) (x' : A) : (term382 A B f x') = (term383 A B f x').
Proof. exact (MK_COMB (@lem5984343 B) (@lem5984351 A B f x')). Qed.
Lemma lem5984361 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) : ((f x') = (g x')) = ((@I (A -> B) f x') = (@I (A -> B) g x')).
Proof. exact (MK_COMB (@lem5984360 A B f x') (@lem5984359 A B g x')). Qed.
Lemma lem5984362 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) : (term114 A B f g x') = (term428 A B f g x').
Proof. exact (MK_COMB (@lem5984342) (@lem5984361 A B f g x')). Qed.
Lemma lem5984369 {A : Type'} (x' : A) (t : A -> Prop) : (term396 A x' t) = (term396 A x' t).
Proof. exact (eq_refl (term396 A x' t)). Qed.
Lemma lem5984370 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) : (term643 A B t f g x') = (term837 A B t f g x').
Proof. exact (MK_COMB (@lem5984369 A x' t) (@lem5984362 A B f g x')). Qed.
Lemma lem5984371 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5984372 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) : (term697 A B t f g x') = (term838 A B t f g x').
Proof. exact (MK_COMB (@lem5984371) (@lem5984370 A B t f g x')). Qed.
Lemma lem5984373 {A B : Type'} (x' : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term699 A B x' f op t g) = (term839 A B x' f op t g).
Proof. exact (MK_COMB (@lem5984372 A B t f g x') (@lem5984341 A B f op t g)). Qed.
Lemma lem5984374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5984375 {A B : Type'} (x' : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term716 A B x' f op t g) = (term840 A B x' f op t g).
Proof. exact (MK_COMB (@lem5984374) (@lem5984373 A B x' f op t g)). Qed.
Lemma lem5984376 {A B : Type'} (x' : A) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term718 A B x' f op g x t) = (term841 A B x' f op g x t).
Proof. exact (MK_COMB (@lem5984375 A B x' f op t g) (@lem5984324 A x t)). Qed.
Lemma lem5984377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5984378 {A B : Type'} (x' : A) (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) (t : A -> Prop) : (term733 A B x' f op g x t) = (term842 A B x' f op g x t).
Proof. exact (MK_COMB (@lem5984377) (@lem5984376 A B x' f op g x t)). Qed.
Lemma lem5984379 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term735 A B x' f x op t g) = (term843 A B x' f x op t g).
Proof. exact (MK_COMB (@lem5984378 A B x' f op g x t) (@lem5984311 A B f x op t g)). Qed.
Lemma lem5984380 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term843 A B x' f x op t g.
Proof. exact (EQ_MP (@lem5984379 A B x' f x op t g) (@lem5984052 A B x' f x op t g h1)). Qed.
Lemma lem5984381 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term836 A B f x op t g.
Proof. exact (proj2 (@lem5984380 A B x' f x op t g h1)). Qed.
Lemma lem5984382 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term841 A B x' f op g x t.
Proof. exact (proj1 (@lem5984380 A B x' f x op t g h1)). Qed.
Lemma lem5984384 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term834 A B x t f g.
Proof. exact (proj1 (@lem5984381 A B x' f x op t g h1)). Qed.
Lemma lem5984386 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term839 A B x' f op t g.
Proof. exact (proj1 (@lem5984382 A B x' f x op t g h1)). Qed.
Lemma lem5984392 {A : Type'} (h1 : term608 A) : term816 A.
Proof. exact (proj1 (@lem5984130 A h1)). Qed.
Lemma lem5984393 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term837 A B t f g x') : term837 A B t f g x'.
Proof. exact (h1). Qed.
Lemma lem5984404 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) : (term832 A B x t f g x') = (term832 A B x t f g x').
Proof. exact (eq_refl (term832 A B x t f g x')). Qed.
Lemma lem5984405 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term833 A B x t f g) = (term833 A B x t f g).
Proof. exact (fun_ext (fun x' : A => @lem5984404 A B x t f g x')). Qed.
Lemma lem5984406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5984408 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term834 A B x t f g) = (term834 A B x t f g).
Proof. exact (MK_COMB (@lem5984406 A) (@lem5984405 A B x t f g)). Qed.
Lemma lem5984409 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term834 A B x t f g.
Proof. exact (EQ_MP (@lem5984408 A B x t f g) (@lem5984384 A B x' f x op t g h1)). Qed.
Lemma lem5984493 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term748 A y x s) = (term844 A y x s).
Proof. exact (@lem19490 (term118 A x y) (term632 A x y s) (term98 A x s)). Qed.
Lemma lem5984494 {A : Type'} (y : A) (x : A) : (term761 A y x) = (term845 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5984493 A y x s)). Qed.
Lemma lem5984495 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5984496 {A : Type'} (y : A) (x : A) : (term772 A y x) = (term846 A y x).
Proof. exact (MK_COMB (@lem5984495 A) (@lem5984494 A y x)). Qed.
Lemma lem5984497 {A : Type'} (x : A) : (term783 A x) = (term847 A x).
Proof. exact (fun_ext (fun y : A => @lem5984496 A y x)). Qed.
Lemma lem5984498 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5984499 {A : Type'} (x : A) : (term794 A x) = (term848 A x).
Proof. exact (MK_COMB (@lem5984498 A) (@lem5984497 A x)). Qed.
Lemma lem5984500 {A : Type'} : (term805 A) = (term849 A).
Proof. exact (fun_ext (fun x : A => @lem5984499 A x)). Qed.
Lemma lem5984501 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5984503 {A : Type'} : (term816 A) = (term850 A).
Proof. exact (MK_COMB (@lem5984501 A) (@lem5984500 A)). Qed.
Lemma lem5984504 {A : Type'} (h1 : term608 A) : term850 A.
Proof. exact (EQ_MP (@lem5984503 A) (@lem5984392 A h1)). Qed.
Lemma lem5984545 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) : (term832 A B x t f g x') = (term832 A B x t f g x').
Proof. exact (eq_refl (term832 A B x t f g x')). Qed.
Lemma lem5984546 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term833 A B x t f g) = (term833 A B x t f g).
Proof. exact (fun_ext (fun x' : A => @lem5984545 A B x t f g x')). Qed.
Lemma lem5984547 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5984549 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) : (term834 A B x t f g) = (term834 A B x t f g).
Proof. exact (MK_COMB (@lem5984547 A) (@lem5984546 A B x t f g)). Qed.
Lemma lem5984550 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term834 A B x t f g.
Proof. exact (EQ_MP (@lem5984549 A B x t f g) (@lem5984384 A B x' f x op t g h1)). Qed.
Lemma lem5984634 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term748 A y x s) = (term844 A y x s).
Proof. exact (@lem19490 (term118 A x y) (term632 A x y s) (term98 A x s)). Qed.
Lemma lem5984635 {A : Type'} (y : A) (x : A) : (term761 A y x) = (term845 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5984634 A y x s)). Qed.
Lemma lem5984636 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5984637 {A : Type'} (y : A) (x : A) : (term772 A y x) = (term846 A y x).
Proof. exact (MK_COMB (@lem5984636 A) (@lem5984635 A y x)). Qed.
Lemma lem5984638 {A : Type'} (x : A) : (term783 A x) = (term847 A x).
Proof. exact (fun_ext (fun y : A => @lem5984637 A y x)). Qed.
Lemma lem5984639 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5984640 {A : Type'} (x : A) : (term794 A x) = (term848 A x).
Proof. exact (MK_COMB (@lem5984639 A) (@lem5984638 A x)). Qed.
Lemma lem5984641 {A : Type'} : (term805 A) = (term849 A).
Proof. exact (fun_ext (fun x : A => @lem5984640 A x)). Qed.
Lemma lem5984642 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5984644 {A : Type'} : (term816 A) = (term850 A).
Proof. exact (MK_COMB (@lem5984642 A) (@lem5984641 A)). Qed.
Lemma lem5984645 {A : Type'} (h1 : term608 A) : term850 A.
Proof. exact (EQ_MP (@lem5984644 A) (@lem5984392 A h1)). Qed.
Lemma lem5984674 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : (@iterate B A op t f) = (@iterate B A op t g)) : (@iterate B A op t f) = (@iterate B A op t g).
Proof. exact (h1). Qed.
Lemma lem5984675 {A B : Type'} (_75946 : A) (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term851 A B x t f g _75946.
Proof. exact (@lem5984409 A B x' f x op t g h1 _75946). Qed.
Lemma lem5984676 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (_75946 : A) : (term851 A B x t f g _75946) = (term832 A B x t f g _75946).
Proof. exact (eq_refl (term851 A B x t f g _75946)). Qed.
Lemma lem5984696 {A : Type'} (_75953 : A) (h1 : term608 A) : term852 A _75953.
Proof. exact (@lem5984504 A h1 _75953). Qed.
Lemma lem5984697 {A : Type'} (_75953 : A) : (term852 A _75953) = (term848 A _75953).
Proof. exact (eq_refl (term852 A _75953)). Qed.
Lemma lem5984698 {A : Type'} (_75953 : A) (h1 : term608 A) : term848 A _75953.
Proof. exact (EQ_MP (@lem5984697 A _75953) (@lem5984696 A _75953 h1)). Qed.
Lemma lem5984699 {A : Type'} (_75953 : A) (_75954 : A) (h1 : term608 A) : term853 A _75953 _75954.
Proof. exact (@lem5984698 A _75953 h1 _75954). Qed.
Lemma lem5984700 {A : Type'} (_75954 : A) (_75953 : A) : (term853 A _75953 _75954) = (term846 A _75954 _75953).
Proof. exact (eq_refl (term853 A _75953 _75954)). Qed.
Lemma lem5984701 {A : Type'} (_75954 : A) (_75953 : A) (h1 : term608 A) : term846 A _75954 _75953.
Proof. exact (EQ_MP (@lem5984700 A _75954 _75953) (@lem5984699 A _75953 _75954 h1)). Qed.
Lemma lem5984702 {A : Type'} (_75954 : A) (_75953 : A) (_75955 : A -> Prop) (h1 : term608 A) : term854 A _75954 _75953 _75955.
Proof. exact (@lem5984701 A _75954 _75953 h1 _75955). Qed.
Lemma lem5984703 {A : Type'} (_75954 : A) (_75953 : A) (_75955 : A -> Prop) : (term854 A _75954 _75953 _75955) = (term844 A _75954 _75953 _75955).
Proof. exact (eq_refl (term854 A _75954 _75953 _75955)). Qed.
Lemma lem5984704 {A : Type'} (_75954 : A) (_75953 : A) (_75955 : A -> Prop) (h1 : term608 A) : term844 A _75954 _75953 _75955.
Proof. exact (EQ_MP (@lem5984703 A _75954 _75953 _75955) (@lem5984702 A _75954 _75953 _75955 h1)). Qed.
Lemma lem5984714 {A B : Type'} (_75959 : A) (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term851 A B x t f g _75959.
Proof. exact (@lem5984550 A B x' f x op t g h1 _75959). Qed.
Lemma lem5984715 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (_75959 : A) : (term851 A B x t f g _75959) = (term832 A B x t f g _75959).
Proof. exact (eq_refl (term851 A B x t f g _75959)). Qed.
Lemma lem5984735 {A : Type'} (_75966 : A) (h1 : term608 A) : term852 A _75966.
Proof. exact (@lem5984645 A h1 _75966). Qed.
Lemma lem5984736 {A : Type'} (_75966 : A) : (term852 A _75966) = (term848 A _75966).
Proof. exact (eq_refl (term852 A _75966)). Qed.
Lemma lem5984737 {A : Type'} (_75966 : A) (h1 : term608 A) : term848 A _75966.
Proof. exact (EQ_MP (@lem5984736 A _75966) (@lem5984735 A _75966 h1)). Qed.
Lemma lem5984738 {A : Type'} (_75966 : A) (_75967 : A) (h1 : term608 A) : term853 A _75966 _75967.
Proof. exact (@lem5984737 A _75966 h1 _75967). Qed.
Lemma lem5984739 {A : Type'} (_75967 : A) (_75966 : A) : (term853 A _75966 _75967) = (term846 A _75967 _75966).
Proof. exact (eq_refl (term853 A _75966 _75967)). Qed.
Lemma lem5984740 {A : Type'} (_75967 : A) (_75966 : A) (h1 : term608 A) : term846 A _75967 _75966.
Proof. exact (EQ_MP (@lem5984739 A _75967 _75966) (@lem5984738 A _75966 _75967 h1)). Qed.
Lemma lem5984741 {A : Type'} (_75967 : A) (_75966 : A) (_75968 : A -> Prop) (h1 : term608 A) : term854 A _75967 _75966 _75968.
Proof. exact (@lem5984740 A _75967 _75966 h1 _75968). Qed.
Lemma lem5984742 {A : Type'} (_75967 : A) (_75966 : A) (_75968 : A -> Prop) : (term854 A _75967 _75966 _75968) = (term844 A _75967 _75966 _75968).
Proof. exact (eq_refl (term854 A _75967 _75966 _75968)). Qed.
Lemma lem5984743 {A : Type'} (_75967 : A) (_75966 : A) (_75968 : A -> Prop) (h1 : term608 A) : term844 A _75967 _75966 _75968.
Proof. exact (EQ_MP (@lem5984742 A _75967 _75966 _75968) (@lem5984741 A _75967 _75966 _75968 h1)). Qed.
Lemma lem5984766 {A B : Type'} (_75946 : A) (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term832 A B x t f g _75946.
Proof. exact (EQ_MP (@lem5984676 A B x t f g _75946) (@lem5984675 A B _75946 x' f x op t g h1)). Qed.
Lemma lem5984796 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term837 A B t f g x') : term428 A B f g x'.
Proof. exact (proj2 (@lem5984393 A B t f g x' h1)). Qed.
Lemma lem5984808 {A : Type'} (_75954 : A) (_75953 : A) (_75955 : A -> Prop) (h1 : term608 A) : term855 A _75954 _75953 _75955.
Proof. exact (proj2 (@lem5984704 A _75954 _75953 _75955 h1)). Qed.
Lemma lem5984826 {A B : Type'} (_75959 : A) (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term832 A B x t f g _75959.
Proof. exact (EQ_MP (@lem5984715 A B x t f g _75959) (@lem5984714 A B _75959 x' f x op t g h1)). Qed.
Lemma lem5984828 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term830 A B f x op t g.
Proof. exact (proj2 (@lem5984381 A B x' f x op t g h1)). Qed.
Lemma lem5984854 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : (@iterate B A op t f) = (@iterate B A op t g)) : (@iterate B A op t f) = (@iterate B A op t g).
Proof. exact (h1). Qed.
Lemma lem5984860 {A : Type'} (_75968 : A -> Prop) (_75966 : A) (_75967 : A) (h1 : term608 A) : term856 A _75968 _75966 _75967.
Proof. exact (proj1 (@lem5984743 A _75967 _75966 _75968 h1)). Qed.
Lemma lem5985041 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term837 A B t f g x') : @IN A x' t.
Proof. exact (proj1 (@lem5984393 A B t f g x' h1)). Qed.
Lemma lem5985042 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term837 A B t f g x') : term100 A x' t.
Proof. exact (fun h0 : term98 A x' t => @lem5985041 A B t f g x' h1). Qed.
Lemma lem5985044 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5985045 {A : Type'} (x' : A) (t : A -> Prop) : (term100 A x' t) = (@IN A x' t).
Proof. exact (@lem5985044 (@IN A x' t)). Qed.
Lemma lem5985046 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term837 A B t f g x') : @IN A x' t.
Proof. exact (EQ_MP (@lem5985045 A x' t) (@lem5985042 A B t f g x' h1)). Qed.
Lemma lem5985048 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5985049 {A : Type'} (_75953 : A) (_75954 : A) (_75955 : A -> Prop) : (term855 A _75954 _75953 _75955) = (term857 A _75953 _75954 _75955).
Proof. exact (@lem5985048 (term98 A _75953 _75955) (term632 A _75953 _75954 _75955)). Qed.
Lemma lem5985051 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5985052 {A : Type'} (_75953 : A) (_75955 : A -> Prop) : (term110 A _75953 _75955) = (@IN A _75953 _75955).
Proof. exact (@lem5985051 (@IN A _75953 _75955)). Qed.
Lemma lem5985053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5985054 {A : Type'} (_75953 : A) (_75955 : A -> Prop) : (term111 A _75953 _75955) = (term112 A _75953 _75955).
Proof. exact (MK_COMB (@lem5985053) (@lem5985052 A _75953 _75955)). Qed.
Lemma lem5985055 {A : Type'} (_75953 : A) (_75954 : A) (_75955 : A -> Prop) : (term632 A _75953 _75954 _75955) = (term632 A _75953 _75954 _75955).
Proof. exact (eq_refl (term632 A _75953 _75954 _75955)). Qed.
Lemma lem5985056 {A : Type'} (_75953 : A) (_75954 : A) (_75955 : A -> Prop) : (term857 A _75953 _75954 _75955) = (term858 A _75953 _75954 _75955).
Proof. exact (MK_COMB (@lem5985054 A _75953 _75955) (@lem5985055 A _75953 _75954 _75955)). Qed.
Lemma lem5985057 {A : Type'} (_75953 : A) (_75954 : A) (_75955 : A -> Prop) : (term855 A _75954 _75953 _75955) = (term858 A _75953 _75954 _75955).
Proof. exact (TRANS (@lem5985049 A _75953 _75954 _75955) (@lem5985056 A _75953 _75954 _75955)). Qed.
Lemma lem5985060 {A : Type'} (_75953 : A) (_75954 : A) (_75955 : A -> Prop) (h1 : term608 A) : term858 A _75953 _75954 _75955.
Proof. exact (EQ_MP (@lem5985057 A _75953 _75954 _75955) (@lem5984808 A _75954 _75953 _75955 h1)). Qed.
Lemma lem5985061 {A : Type'} (_75953 : A) (_75954 : A) (_75955 : A -> Prop) (h1 : term608 A) : term858 A _75953 _75954 _75955.
Proof. exact (@lem5985060 A _75953 _75954 _75955 h1). Qed.
Lemma lem5985062 {A : Type'} (x' : A) (_75954 : A) (t : A -> Prop) (h1 : term608 A) : term858 A x' _75954 t.
Proof. exact (@lem5985061 A x' _75954 t h1). Qed.
Lemma lem5985065 {A B : Type'} (_75954 : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term608 A) (h2 : term837 A B t f g x') : term632 A x' _75954 t.
Proof. exact (@lem5985062 A x' _75954 t h1 (@lem5985046 A B t f g x' h2)). Qed.
Lemma lem5985066 {A B : Type'} (_75954 : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term608 A) (h2 : term837 A B t f g x') : term632 A x' _75954 t.
Proof. exact (@lem5985065 A B _75954 t f g x' h1 h2). Qed.
Lemma lem5985067 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term608 A) (h2 : term837 A B t f g x') : term632 A x' x t.
Proof. exact (@lem5985066 A B x t f g x' h1 h2). Qed.
Lemma lem5985068 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term608 A) (h2 : term837 A B t f g x') : term859 A x' x t.
Proof. exact (fun h0 : term860 A x' x t => @lem5985067 A B x t f g x' h1 h2). Qed.
Lemma lem5985070 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5985071 {A : Type'} (x' : A) (x : A) (t : A -> Prop) : (term859 A x' x t) = (term632 A x' x t).
Proof. exact (@lem5985070 (term632 A x' x t)). Qed.
Lemma lem5985072 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term608 A) (h2 : term837 A B t f g x') : term632 A x' x t.
Proof. exact (EQ_MP (@lem5985071 A x' x t) (@lem5985068 A B x t f g x' h1 h2)). Qed.
Lemma lem5985078 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5985079 {A B : Type'} (f : A -> B) (g : A -> B) (_75946 : A) (x : A) (t : A -> Prop) : (term832 A B x t f g _75946) = (term861 A B f g _75946 x t).
Proof. exact (@lem5985078 ((@I (A -> B) f _75946) = (@I (A -> B) g _75946)) (term860 A _75946 x t)). Qed.
Lemma lem5985087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5985088 {A B : Type'} (f : A -> B) (g : A -> B) (_75946 : A) (x : A) (t : A -> Prop) : (term862 A B x t f g _75946) = (term863 A B f g _75946 x t).
Proof. exact (MK_COMB (@lem5985087) (@lem5985079 A B f g _75946 x t)). Qed.
Lemma lem5985096 {A B : Type'} (f : A -> B) (g : A -> B) (_75946 : A) (x : A) (t : A -> Prop) : (term861 A B f g _75946 x t) = (term861 A B f g _75946 x t).
Proof. exact (eq_refl (term861 A B f g _75946 x t)). Qed.
Lemma lem5985097 {A B : Type'} (f : A -> B) (g : A -> B) (_75946 : A) (x : A) (t : A -> Prop) : ((term832 A B x t f g _75946) = (term861 A B f g _75946 x t)) = ((term861 A B f g _75946 x t) = (term861 A B f g _75946 x t)).
Proof. exact (MK_COMB (@lem5985088 A B f g _75946 x t) (@lem5985096 A B f g _75946 x t)). Qed.
Lemma lem5985099 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5985100 (x : Prop) : (x = x) = True.
Proof. exact (@lem5985099 Prop x). Qed.
Lemma lem5985101 {A B : Type'} (f : A -> B) (g : A -> B) (_75946 : A) (x : A) (t : A -> Prop) : ((term861 A B f g _75946 x t) = (term861 A B f g _75946 x t)) = True.
Proof. exact (@lem5985100 (term861 A B f g _75946 x t)). Qed.
Lemma lem5985102 {A B : Type'} (f : A -> B) (g : A -> B) (_75946 : A) (x : A) (t : A -> Prop) : ((term832 A B x t f g _75946) = (term861 A B f g _75946 x t)) = True.
Proof. exact (TRANS (@lem5985097 A B f g _75946 x t) (@lem5985101 A B f g _75946 x t)). Qed.
Lemma lem5985103 {A B : Type'} (f : A -> B) (g : A -> B) (_75946 : A) (x : A) (t : A -> Prop) : True = ((term832 A B x t f g _75946) = (term861 A B f g _75946 x t)).
Proof. exact (SYM (@lem5985102 A B f g _75946 x t)). Qed.
Lemma lem5985104 {A B : Type'} (f : A -> B) (g : A -> B) (_75946 : A) (x : A) (t : A -> Prop) : (term832 A B x t f g _75946) = (term861 A B f g _75946 x t).
Proof. exact (EQ_MP (@lem5985103 A B f g _75946 x t) (@lem0)). Qed.
Lemma lem5985105 {A B : Type'} (_75946 : A) (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term861 A B f g _75946 x t.
Proof. exact (EQ_MP (@lem5985104 A B f g _75946 x t) (@lem5984766 A B _75946 x' f x op t g h1)). Qed.
Lemma lem5985107 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5985108 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (_75946 : A) : (term861 A B f g _75946 x t) = (term864 A B x t f g _75946).
Proof. exact (@lem5985107 (term860 A _75946 x t) ((@I (A -> B) f _75946) = (@I (A -> B) g _75946))). Qed.
Lemma lem5985110 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5985111 {A : Type'} (_75946 : A) (x : A) (t : A -> Prop) : (term865 A _75946 x t) = (term632 A _75946 x t).
Proof. exact (@lem5985110 (term632 A _75946 x t)). Qed.
Lemma lem5985112 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5985113 {A : Type'} (_75946 : A) (x : A) (t : A -> Prop) : (term866 A _75946 x t) = (term867 A _75946 x t).
Proof. exact (MK_COMB (@lem5985112) (@lem5985111 A _75946 x t)). Qed.
Lemma lem5985114 {A B : Type'} (f : A -> B) (g : A -> B) (_75946 : A) : ((@I (A -> B) f _75946) = (@I (A -> B) g _75946)) = ((@I (A -> B) f _75946) = (@I (A -> B) g _75946)).
Proof. exact (eq_refl ((@I (A -> B) f _75946) = (@I (A -> B) g _75946))). Qed.
Lemma lem5985115 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (_75946 : A) : (term864 A B x t f g _75946) = (term868 A B x t f g _75946).
Proof. exact (MK_COMB (@lem5985113 A _75946 x t) (@lem5985114 A B f g _75946)). Qed.
Lemma lem5985116 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (_75946 : A) : (term861 A B f g _75946 x t) = (term868 A B x t f g _75946).
Proof. exact (TRANS (@lem5985108 A B x t f g _75946) (@lem5985115 A B x t f g _75946)). Qed.
Lemma lem5985119 {A B : Type'} (_75946 : A) (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term868 A B x t f g _75946.
Proof. exact (EQ_MP (@lem5985116 A B x t f g _75946) (@lem5985105 A B _75946 x' f x op t g h1)). Qed.
Lemma lem5985120 {A B : Type'} (_75946 : A) (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term868 A B x t f g _75946.
Proof. exact (@lem5985119 A B _75946 x' f x op t g h1). Qed.
Lemma lem5985121 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term868 A B x t f g x'.
Proof. exact (@lem5985120 A B x' x' f x op t g h1). Qed.
Lemma lem5985124 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : term837 A B t f g x') : (@I (A -> B) f x') = (@I (A -> B) g x').
Proof. exact (@lem5985121 A B x' f x op t g h2 (@lem5985072 A B x t f g x' h1 h3)). Qed.
Lemma lem5985125 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : term837 A B t f g x') : term470 A B f g x'.
Proof. exact (fun h0 : term428 A B f g x' => @lem5985124 A B x op t f g x' h1 h2 h3). Qed.
Lemma lem5985127 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5985128 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) : (term470 A B f g x') = ((@I (A -> B) f x') = (@I (A -> B) g x')).
Proof. exact (@lem5985127 ((@I (A -> B) f x') = (@I (A -> B) g x'))). Qed.
Lemma lem5985129 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : term837 A B t f g x') : (@I (A -> B) f x') = (@I (A -> B) g x').
Proof. exact (EQ_MP (@lem5985128 A B f g x') (@lem5985125 A B x op t f g x' h1 h2 h3)). Qed.
Lemma lem5985132 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5985134 {A B : Type'} (f : A -> B) (g : A -> B) (x' : A) : (term428 A B f g x') = (term471 A B f g x').
Proof. exact (@lem5985132 ((@I (A -> B) f x') = (@I (A -> B) g x'))). Qed.
Lemma lem5985137 {A B : Type'} (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term837 A B t f g x') : term471 A B f g x'.
Proof. exact (EQ_MP (@lem5985134 A B f g x') (@lem5984796 A B t f g x' h1)). Qed.
Lemma lem5985140 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : term837 A B t f g x') : False.
Proof. exact (@lem5985137 A B t f g x' h3 (@lem5985129 A B x op t f g x' h1 h2 h3)). Qed.
Lemma lem5985141 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : term837 A B t f g x') : term103.
Proof. exact (fun h0 : ~ False => @lem5985140 A B x op t f g x' h1 h2 h3). Qed.
Lemma lem5985143 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5985144 : term103 = False.
Proof. exact (@lem5985143 False). Qed.
Lemma lem5985145 {A B : Type'} (x : A) (op : type1400 B) (t : A -> Prop) (f : A -> B) (g : A -> B) (x' : A) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : term837 A B t f g x') : False.
Proof. exact (EQ_MP (@lem5985144) (@lem5985141 A B x op t f g x' h1 h2 h3)). Qed.
Lemma lem5985211 {B : Type'} : (@I (B -> B -> B)) = (@I (B -> B -> B)).
Proof. exact (eq_refl (@I (B -> B -> B))). Qed.
Lemma lem5985212 {B : Type'} (_76022 : type1400 B) (_76024 : type1400 B) (h1 : _76022 = _76024) : _76022 = _76024.
Proof. exact (h1). Qed.
Lemma lem5985213 {B : Type'} (_76023 : B) (_76025 : B) (h1 : _76023 = _76025) : _76023 = _76025.
Proof. exact (h1). Qed.
Lemma lem5985214 {B : Type'} (_76022 : type1400 B) (_76024 : type1400 B) (h1 : _76022 = _76024) : (@I (B -> B -> B) _76022) = (@I (B -> B -> B) _76024).
Proof. exact (MK_COMB (@lem5985211 B) (@lem5985212 B _76022 _76024 h1)). Qed.
Lemma lem5985215 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) (h1 : _76023 = _76025) (h2 : _76022 = _76024) : (@I (B -> B -> B) _76022 _76023) = (@I (B -> B -> B) _76024 _76025).
Proof. exact (MK_COMB (@lem5985214 B _76022 _76024 h2) (@lem5985213 B _76023 _76025 h1)). Qed.
Lemma lem5985216 {B : Type'} (_76022 : type1400 B) (_76024 : type1400 B) (_76023 : B) (_76025 : B) (h1 : _76023 = _76025) : term869 B _76022 _76023 _76024 _76025.
Proof. exact (fun h0 : _76022 = _76024 => @lem5985215 B _76023 _76025 _76022 _76024 h1 h0). Qed.
Lemma lem5985218 (a : Prop) (b : Prop) : (a -> b) = (term870 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5985219 {B : Type'} (_76022 : type1400 B) (_76023 : B) (_76024 : type1400 B) (_76025 : B) : (term869 B _76022 _76023 _76024 _76025) = (term871 B _76022 _76023 _76024 _76025).
Proof. exact (@lem5985218 (_76022 = _76024) ((@I (B -> B -> B) _76022 _76023) = (@I (B -> B -> B) _76024 _76025))). Qed.
Lemma lem5985220 {B : Type'} (_76022 : type1400 B) (_76024 : type1400 B) (_76023 : B) (_76025 : B) (h1 : _76023 = _76025) : term871 B _76022 _76023 _76024 _76025.
Proof. exact (EQ_MP (@lem5985219 B _76022 _76023 _76024 _76025) (@lem5985216 B _76022 _76024 _76023 _76025 h1)). Qed.
Lemma lem5985221 {B : Type'} (_76022 : type1400 B) (_76023 : B) (_76024 : type1400 B) (_76025 : B) : term872 B _76022 _76023 _76024 _76025.
Proof. exact (fun h0 : _76023 = _76025 => @lem5985220 B _76022 _76024 _76023 _76025 h0). Qed.
Lemma lem5985223 (a : Prop) (b : Prop) : (a -> b) = (term870 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5985224 {B : Type'} (_76022 : type1400 B) (_76023 : B) (_76024 : type1400 B) (_76025 : B) : (term872 B _76022 _76023 _76024 _76025) = (term873 B _76022 _76023 _76024 _76025).
Proof. exact (@lem5985223 (_76023 = _76025) (term871 B _76022 _76023 _76024 _76025)). Qed.
Lemma lem5985225 {B : Type'} (_76022 : type1400 B) (_76023 : B) (_76024 : type1400 B) (_76025 : B) : term873 B _76022 _76023 _76024 _76025.
Proof. exact (EQ_MP (@lem5985224 B _76022 _76023 _76024 _76025) (@lem5985221 B _76022 _76023 _76024 _76025)). Qed.
Lemma lem5985248 {B : Type'} : (@I (B -> B)) = (@I (B -> B)).
Proof. exact (eq_refl (@I (B -> B))). Qed.
Lemma lem5985249 {B : Type'} (_76032 : B -> B) (_76034 : B -> B) (h1 : _76032 = _76034) : _76032 = _76034.
Proof. exact (h1). Qed.
Lemma lem5985250 {B : Type'} (_76033 : B) (_76035 : B) (h1 : _76033 = _76035) : _76033 = _76035.
Proof. exact (h1). Qed.
Lemma lem5985251 {B : Type'} (_76032 : B -> B) (_76034 : B -> B) (h1 : _76032 = _76034) : (@I (B -> B) _76032) = (@I (B -> B) _76034).
Proof. exact (MK_COMB (@lem5985248 B) (@lem5985249 B _76032 _76034 h1)). Qed.
Lemma lem5985252 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) (h1 : _76033 = _76035) (h2 : _76032 = _76034) : (@I (B -> B) _76032 _76033) = (@I (B -> B) _76034 _76035).
Proof. exact (MK_COMB (@lem5985251 B _76032 _76034 h2) (@lem5985250 B _76033 _76035 h1)). Qed.
Lemma lem5985253 {B : Type'} (_76032 : B -> B) (_76034 : B -> B) (_76033 : B) (_76035 : B) (h1 : _76033 = _76035) : term874 B _76032 _76033 _76034 _76035.
Proof. exact (fun h0 : _76032 = _76034 => @lem5985252 B _76033 _76035 _76032 _76034 h1 h0). Qed.
Lemma lem5985255 (a : Prop) (b : Prop) : (a -> b) = (term870 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5985256 {B : Type'} (_76032 : B -> B) (_76033 : B) (_76034 : B -> B) (_76035 : B) : (term874 B _76032 _76033 _76034 _76035) = (term875 B _76032 _76033 _76034 _76035).
Proof. exact (@lem5985255 (_76032 = _76034) ((@I (B -> B) _76032 _76033) = (@I (B -> B) _76034 _76035))). Qed.
Lemma lem5985257 {B : Type'} (_76032 : B -> B) (_76034 : B -> B) (_76033 : B) (_76035 : B) (h1 : _76033 = _76035) : term875 B _76032 _76033 _76034 _76035.
Proof. exact (EQ_MP (@lem5985256 B _76032 _76033 _76034 _76035) (@lem5985253 B _76032 _76034 _76033 _76035 h1)). Qed.
Lemma lem5985258 {B : Type'} (_76032 : B -> B) (_76033 : B) (_76034 : B -> B) (_76035 : B) : term876 B _76032 _76033 _76034 _76035.
Proof. exact (fun h0 : _76033 = _76035 => @lem5985257 B _76032 _76034 _76033 _76035 h0). Qed.
Lemma lem5985260 (a : Prop) (b : Prop) : (a -> b) = (term870 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5985261 {B : Type'} (_76032 : B -> B) (_76033 : B) (_76034 : B -> B) (_76035 : B) : (term876 B _76032 _76033 _76034 _76035) = (term877 B _76032 _76033 _76034 _76035).
Proof. exact (@lem5985260 (_76033 = _76035) (term875 B _76032 _76033 _76034 _76035)). Qed.
Lemma lem5985262 {B : Type'} (_76032 : B -> B) (_76033 : B) (_76034 : B -> B) (_76035 : B) : term877 B _76032 _76033 _76034 _76035.
Proof. exact (EQ_MP (@lem5985261 B _76032 _76033 _76034 _76035) (@lem5985258 B _76032 _76033 _76034 _76035)). Qed.
Lemma lem5985308 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : (@iterate B A op t f) = (@iterate B A op t g)) : (@iterate B A op t f) = (@iterate B A op t g).
Proof. exact (h1). Qed.
Lemma lem5985309 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : (@iterate B A op t f) = (@iterate B A op t g)) : term878 A B f op t g.
Proof. exact (fun h0 : term879 A B f op t g => @lem5985308 A B f op t g h1). Qed.
Lemma lem5985311 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5985312 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term878 A B f op t g) = ((@iterate B A op t f) = (@iterate B A op t g)).
Proof. exact (@lem5985311 ((@iterate B A op t f) = (@iterate B A op t g))). Qed.
Lemma lem5985313 {A B : Type'} (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : (@iterate B A op t f) = (@iterate B A op t g)) : (@iterate B A op t f) = (@iterate B A op t g).
Proof. exact (EQ_MP (@lem5985312 A B f op t g) (@lem5985309 A B f op t g h1)). Qed.
Lemma lem5985315 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5985316 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5985315 A x). Qed.
Lemma lem5985317 {A : Type'} (x : A) : term880 A x.
Proof. exact (fun h0 : term881 A x => @lem5985316 A x). Qed.
Lemma lem5985319 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5985320 {A : Type'} (x : A) : (term880 A x) = (x = x).
Proof. exact (@lem5985319 (x = x)). Qed.
Lemma lem5985321 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem5985320 A x) (@lem5985317 A x)). Qed.
Lemma lem5985323 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5985324 {A : Type'} (_75966 : A) (_75967 : A) (_75968 : A -> Prop) : (term856 A _75968 _75966 _75967) = (term882 A _75966 _75967 _75968).
Proof. exact (@lem5985323 (term118 A _75966 _75967) (term632 A _75966 _75967 _75968)). Qed.
Lemma lem5985326 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5985327 {A : Type'} (_75966 : A) (_75967 : A) : (term131 A _75966 _75967) = (_75966 = _75967).
Proof. exact (@lem5985326 (_75966 = _75967)). Qed.
Lemma lem5985328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5985329 {A : Type'} (_75966 : A) (_75967 : A) : (term883 A _75966 _75967) = (term884 A _75966 _75967).
Proof. exact (MK_COMB (@lem5985328) (@lem5985327 A _75966 _75967)). Qed.
Lemma lem5985330 {A : Type'} (_75966 : A) (_75967 : A) (_75968 : A -> Prop) : (term632 A _75966 _75967 _75968) = (term632 A _75966 _75967 _75968).
Proof. exact (eq_refl (term632 A _75966 _75967 _75968)). Qed.
Lemma lem5985331 {A : Type'} (_75966 : A) (_75967 : A) (_75968 : A -> Prop) : (term882 A _75966 _75967 _75968) = (term885 A _75966 _75967 _75968).
Proof. exact (MK_COMB (@lem5985329 A _75966 _75967) (@lem5985330 A _75966 _75967 _75968)). Qed.
Lemma lem5985332 {A : Type'} (_75966 : A) (_75967 : A) (_75968 : A -> Prop) : (term856 A _75968 _75966 _75967) = (term885 A _75966 _75967 _75968).
Proof. exact (TRANS (@lem5985324 A _75966 _75967 _75968) (@lem5985331 A _75966 _75967 _75968)). Qed.
Lemma lem5985335 {A : Type'} (_75966 : A) (_75967 : A) (_75968 : A -> Prop) (h1 : term608 A) : term885 A _75966 _75967 _75968.
Proof. exact (EQ_MP (@lem5985332 A _75966 _75967 _75968) (@lem5984860 A _75968 _75966 _75967 h1)). Qed.
Lemma lem5985336 {A : Type'} (_75966 : A) (_75967 : A) (_75968 : A -> Prop) (h1 : term608 A) : term885 A _75966 _75967 _75968.
Proof. exact (@lem5985335 A _75966 _75967 _75968 h1). Qed.
Lemma lem5985337 {A : Type'} (x : A) (_75968 : A -> Prop) (h1 : term608 A) : term886 A x _75968.
Proof. exact (@lem5985336 A x x _75968 h1). Qed.
Lemma lem5985340 {A : Type'} (x : A) (_75968 : A -> Prop) (h1 : term608 A) : term887 A x _75968.
Proof. exact (@lem5985337 A x _75968 h1 (@lem5985321 A x)). Qed.
Lemma lem5985341 {A : Type'} (x : A) (_75968 : A -> Prop) (h1 : term608 A) : term887 A x _75968.
Proof. exact (@lem5985340 A x _75968 h1). Qed.
Lemma lem5985342 {A : Type'} (x : A) (t : A -> Prop) (h1 : term608 A) : term887 A x t.
Proof. exact (@lem5985341 A x t h1). Qed.
Lemma lem5985343 {A : Type'} (x : A) (t : A -> Prop) (h1 : term608 A) : term888 A x t.
Proof. exact (fun h0 : term889 A x t => @lem5985342 A x t h1). Qed.
Lemma lem5985345 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5985346 {A : Type'} (x : A) (t : A -> Prop) : (term888 A x t) = (term887 A x t).
Proof. exact (@lem5985345 (term887 A x t)). Qed.
Lemma lem5985347 {A : Type'} (x : A) (t : A -> Prop) (h1 : term608 A) : term887 A x t.
Proof. exact (EQ_MP (@lem5985346 A x t) (@lem5985343 A x t h1)). Qed.
Lemma lem5985353 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5985354 {A B : Type'} (f : A -> B) (g : A -> B) (_75959 : A) (x : A) (t : A -> Prop) : (term832 A B x t f g _75959) = (term861 A B f g _75959 x t).
Proof. exact (@lem5985353 ((@I (A -> B) f _75959) = (@I (A -> B) g _75959)) (term860 A _75959 x t)). Qed.
Lemma lem5985362 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5985363 {A B : Type'} (f : A -> B) (g : A -> B) (_75959 : A) (x : A) (t : A -> Prop) : (term862 A B x t f g _75959) = (term863 A B f g _75959 x t).
Proof. exact (MK_COMB (@lem5985362) (@lem5985354 A B f g _75959 x t)). Qed.
Lemma lem5985371 {A B : Type'} (f : A -> B) (g : A -> B) (_75959 : A) (x : A) (t : A -> Prop) : (term861 A B f g _75959 x t) = (term861 A B f g _75959 x t).
Proof. exact (eq_refl (term861 A B f g _75959 x t)). Qed.
Lemma lem5985372 {A B : Type'} (f : A -> B) (g : A -> B) (_75959 : A) (x : A) (t : A -> Prop) : ((term832 A B x t f g _75959) = (term861 A B f g _75959 x t)) = ((term861 A B f g _75959 x t) = (term861 A B f g _75959 x t)).
Proof. exact (MK_COMB (@lem5985363 A B f g _75959 x t) (@lem5985371 A B f g _75959 x t)). Qed.
Lemma lem5985374 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5985375 (x : Prop) : (x = x) = True.
Proof. exact (@lem5985374 Prop x). Qed.
Lemma lem5985376 {A B : Type'} (f : A -> B) (g : A -> B) (_75959 : A) (x : A) (t : A -> Prop) : ((term861 A B f g _75959 x t) = (term861 A B f g _75959 x t)) = True.
Proof. exact (@lem5985375 (term861 A B f g _75959 x t)). Qed.
Lemma lem5985377 {A B : Type'} (f : A -> B) (g : A -> B) (_75959 : A) (x : A) (t : A -> Prop) : ((term832 A B x t f g _75959) = (term861 A B f g _75959 x t)) = True.
Proof. exact (TRANS (@lem5985372 A B f g _75959 x t) (@lem5985376 A B f g _75959 x t)). Qed.
Lemma lem5985378 {A B : Type'} (f : A -> B) (g : A -> B) (_75959 : A) (x : A) (t : A -> Prop) : True = ((term832 A B x t f g _75959) = (term861 A B f g _75959 x t)).
Proof. exact (SYM (@lem5985377 A B f g _75959 x t)). Qed.
Lemma lem5985379 {A B : Type'} (f : A -> B) (g : A -> B) (_75959 : A) (x : A) (t : A -> Prop) : (term832 A B x t f g _75959) = (term861 A B f g _75959 x t).
Proof. exact (EQ_MP (@lem5985378 A B f g _75959 x t) (@lem0)). Qed.
Lemma lem5985380 {A B : Type'} (_75959 : A) (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term861 A B f g _75959 x t.
Proof. exact (EQ_MP (@lem5985379 A B f g _75959 x t) (@lem5984826 A B _75959 x' f x op t g h1)). Qed.
Lemma lem5985382 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5985383 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (_75959 : A) : (term861 A B f g _75959 x t) = (term864 A B x t f g _75959).
Proof. exact (@lem5985382 (term860 A _75959 x t) ((@I (A -> B) f _75959) = (@I (A -> B) g _75959))). Qed.
Lemma lem5985385 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5985386 {A : Type'} (_75959 : A) (x : A) (t : A -> Prop) : (term865 A _75959 x t) = (term632 A _75959 x t).
Proof. exact (@lem5985385 (term632 A _75959 x t)). Qed.
Lemma lem5985387 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5985388 {A : Type'} (_75959 : A) (x : A) (t : A -> Prop) : (term866 A _75959 x t) = (term867 A _75959 x t).
Proof. exact (MK_COMB (@lem5985387) (@lem5985386 A _75959 x t)). Qed.
Lemma lem5985389 {A B : Type'} (f : A -> B) (g : A -> B) (_75959 : A) : ((@I (A -> B) f _75959) = (@I (A -> B) g _75959)) = ((@I (A -> B) f _75959) = (@I (A -> B) g _75959)).
Proof. exact (eq_refl ((@I (A -> B) f _75959) = (@I (A -> B) g _75959))). Qed.
Lemma lem5985390 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (_75959 : A) : (term864 A B x t f g _75959) = (term868 A B x t f g _75959).
Proof. exact (MK_COMB (@lem5985388 A _75959 x t) (@lem5985389 A B f g _75959)). Qed.
Lemma lem5985391 {A B : Type'} (x : A) (t : A -> Prop) (f : A -> B) (g : A -> B) (_75959 : A) : (term861 A B f g _75959 x t) = (term868 A B x t f g _75959).
Proof. exact (TRANS (@lem5985383 A B x t f g _75959) (@lem5985390 A B x t f g _75959)). Qed.
Lemma lem5985394 {A B : Type'} (_75959 : A) (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term868 A B x t f g _75959.
Proof. exact (EQ_MP (@lem5985391 A B x t f g _75959) (@lem5985380 A B _75959 x' f x op t g h1)). Qed.
Lemma lem5985395 {A B : Type'} (_75959 : A) (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term868 A B x t f g _75959.
Proof. exact (@lem5985394 A B _75959 x' f x op t g h1). Qed.
Lemma lem5985396 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term890 A B t f g x.
Proof. exact (@lem5985395 A B x x' f x op t g h1). Qed.
Lemma lem5985399 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) : (@I (A -> B) f x) = (@I (A -> B) g x).
Proof. exact (@lem5985396 A B x' f x op t g h2 (@lem5985347 A x t h1)). Qed.
Lemma lem5985400 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) : term470 A B f g x.
Proof. exact (fun h0 : term428 A B f g x => @lem5985399 A B x' f x op t g h1 h2). Qed.
Lemma lem5985402 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5985403 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term470 A B f g x) = ((@I (A -> B) f x) = (@I (A -> B) g x)).
Proof. exact (@lem5985402 ((@I (A -> B) f x) = (@I (A -> B) g x))). Qed.
Lemma lem5985404 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) : (@I (A -> B) f x) = (@I (A -> B) g x).
Proof. exact (EQ_MP (@lem5985403 A B f g x) (@lem5985400 A B x' f x op t g h1 h2)). Qed.
Lemma lem5985406 {B : Type'} (x : type1400 B) : x = x.
Proof. exact (@lem21386 (type1400 B) x). Qed.
Lemma lem5985407 {B : Type'} (x : type1400 B) : x = x.
Proof. exact (@lem5985406 B x). Qed.
Lemma lem5985408 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (@lem5985407 B op). Qed.
Lemma lem5985409 {B : Type'} (op : type1400 B) : term891 B op.
Proof. exact (fun h0 : term892 B op => @lem5985408 B op). Qed.
Lemma lem5985411 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5985412 {B : Type'} (op : type1400 B) : (term891 B op) = (op = op).
Proof. exact (@lem5985411 (op = op)). Qed.
Lemma lem5985413 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (EQ_MP (@lem5985412 B op) (@lem5985409 B op)). Qed.
Lemma lem5985431 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5985432 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : (term871 B _76022 _76023 _76024 _76025) = (term893 B _76023 _76025 _76022 _76024).
Proof. exact (@lem5985431 ((@I (B -> B -> B) _76022 _76023) = (@I (B -> B -> B) _76024 _76025)) (term894 B _76022 _76024)). Qed.
Lemma lem5985442 {B : Type'} (_76023 : B) (_76025 : B) : (term119 B _76023 _76025) = (term119 B _76023 _76025).
Proof. exact (eq_refl (term119 B _76023 _76025)). Qed.
Lemma lem5985443 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : (term873 B _76022 _76023 _76024 _76025) = (term895 B _76023 _76025 _76022 _76024).
Proof. exact (MK_COMB (@lem5985442 B _76023 _76025) (@lem5985432 B _76023 _76025 _76022 _76024)). Qed.
Lemma lem5985447 (q : Prop) (p : Prop) (r : Prop) : (term121 p q r) = (term121 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5985448 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : (term895 B _76023 _76025 _76022 _76024) = (term896 B _76023 _76025 _76022 _76024).
Proof. exact (@lem5985447 ((@I (B -> B -> B) _76022 _76023) = (@I (B -> B -> B) _76024 _76025)) (term118 B _76023 _76025) (term894 B _76022 _76024)). Qed.
Lemma lem5985470 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : (term873 B _76022 _76023 _76024 _76025) = (term896 B _76023 _76025 _76022 _76024).
Proof. exact (TRANS (@lem5985443 B _76023 _76025 _76022 _76024) (@lem5985448 B _76023 _76025 _76022 _76024)). Qed.
Lemma lem5985471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5985472 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : (term897 B _76022 _76023 _76024 _76025) = (term898 B _76023 _76025 _76022 _76024).
Proof. exact (MK_COMB (@lem5985471) (@lem5985470 B _76023 _76025 _76022 _76024)). Qed.
Lemma lem5985494 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : (term896 B _76023 _76025 _76022 _76024) = (term896 B _76023 _76025 _76022 _76024).
Proof. exact (eq_refl (term896 B _76023 _76025 _76022 _76024)). Qed.
Lemma lem5985495 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : ((term873 B _76022 _76023 _76024 _76025) = (term896 B _76023 _76025 _76022 _76024)) = ((term896 B _76023 _76025 _76022 _76024) = (term896 B _76023 _76025 _76022 _76024)).
Proof. exact (MK_COMB (@lem5985472 B _76023 _76025 _76022 _76024) (@lem5985494 B _76023 _76025 _76022 _76024)). Qed.
Lemma lem5985497 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5985498 (x : Prop) : (x = x) = True.
Proof. exact (@lem5985497 Prop x). Qed.
Lemma lem5985499 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : ((term896 B _76023 _76025 _76022 _76024) = (term896 B _76023 _76025 _76022 _76024)) = True.
Proof. exact (@lem5985498 (term896 B _76023 _76025 _76022 _76024)). Qed.
Lemma lem5985500 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : ((term873 B _76022 _76023 _76024 _76025) = (term896 B _76023 _76025 _76022 _76024)) = True.
Proof. exact (TRANS (@lem5985495 B _76023 _76025 _76022 _76024) (@lem5985499 B _76023 _76025 _76022 _76024)). Qed.
Lemma lem5985501 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : True = ((term873 B _76022 _76023 _76024 _76025) = (term896 B _76023 _76025 _76022 _76024)).
Proof. exact (SYM (@lem5985500 B _76023 _76025 _76022 _76024)). Qed.
Lemma lem5985502 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : (term873 B _76022 _76023 _76024 _76025) = (term896 B _76023 _76025 _76022 _76024).
Proof. exact (EQ_MP (@lem5985501 B _76023 _76025 _76022 _76024) (@lem0)). Qed.
Lemma lem5985503 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : term896 B _76023 _76025 _76022 _76024.
Proof. exact (EQ_MP (@lem5985502 B _76023 _76025 _76022 _76024) (@lem5985225 B _76022 _76023 _76024 _76025)). Qed.
Lemma lem5985505 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5985506 {B : Type'} (_76022 : type1400 B) (_76023 : B) (_76024 : type1400 B) (_76025 : B) : (term896 B _76023 _76025 _76022 _76024) = (term899 B _76022 _76023 _76024 _76025).
Proof. exact (@lem5985505 (term900 B _76023 _76025 _76022 _76024) ((@I (B -> B -> B) _76022 _76023) = (@I (B -> B -> B) _76024 _76025))). Qed.
Lemma lem5985508 (a : Prop) (b : Prop) : (term127 a b) = (term128 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5985509 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : (term901 B _76023 _76025 _76022 _76024) = (term902 B _76023 _76025 _76022 _76024).
Proof. exact (@lem5985508 (term118 B _76023 _76025) (term894 B _76022 _76024)). Qed.
Lemma lem5985511 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5985512 {B : Type'} (_76023 : B) (_76025 : B) : (term131 B _76023 _76025) = (_76023 = _76025).
Proof. exact (@lem5985511 (_76023 = _76025)). Qed.
Lemma lem5985513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5985514 {B : Type'} (_76023 : B) (_76025 : B) : (term132 B _76023 _76025) = (term133 B _76023 _76025).
Proof. exact (MK_COMB (@lem5985513) (@lem5985512 B _76023 _76025)). Qed.
Lemma lem5985516 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5985517 {B : Type'} (_76022 : type1400 B) (_76024 : type1400 B) : (term903 B _76022 _76024) = (_76022 = _76024).
Proof. exact (@lem5985516 (_76022 = _76024)). Qed.
Lemma lem5985518 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : (term902 B _76023 _76025 _76022 _76024) = (term904 B _76023 _76025 _76022 _76024).
Proof. exact (MK_COMB (@lem5985514 B _76023 _76025) (@lem5985517 B _76022 _76024)). Qed.
Lemma lem5985519 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : (term901 B _76023 _76025 _76022 _76024) = (term904 B _76023 _76025 _76022 _76024).
Proof. exact (TRANS (@lem5985509 B _76023 _76025 _76022 _76024) (@lem5985518 B _76023 _76025 _76022 _76024)). Qed.
Lemma lem5985520 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5985521 {B : Type'} (_76023 : B) (_76025 : B) (_76022 : type1400 B) (_76024 : type1400 B) : (term905 B _76023 _76025 _76022 _76024) = (term906 B _76023 _76025 _76022 _76024).
Proof. exact (MK_COMB (@lem5985520) (@lem5985519 B _76023 _76025 _76022 _76024)). Qed.
Lemma lem5985522 {B : Type'} (_76022 : type1400 B) (_76023 : B) (_76024 : type1400 B) (_76025 : B) : ((@I (B -> B -> B) _76022 _76023) = (@I (B -> B -> B) _76024 _76025)) = ((@I (B -> B -> B) _76022 _76023) = (@I (B -> B -> B) _76024 _76025)).
Proof. exact (eq_refl ((@I (B -> B -> B) _76022 _76023) = (@I (B -> B -> B) _76024 _76025))). Qed.
Lemma lem5985523 {B : Type'} (_76022 : type1400 B) (_76023 : B) (_76024 : type1400 B) (_76025 : B) : (term899 B _76022 _76023 _76024 _76025) = (term907 B _76022 _76023 _76024 _76025).
Proof. exact (MK_COMB (@lem5985521 B _76023 _76025 _76022 _76024) (@lem5985522 B _76022 _76023 _76024 _76025)). Qed.
Lemma lem5985524 {B : Type'} (_76022 : type1400 B) (_76023 : B) (_76024 : type1400 B) (_76025 : B) : (term896 B _76023 _76025 _76022 _76024) = (term907 B _76022 _76023 _76024 _76025).
Proof. exact (TRANS (@lem5985506 B _76022 _76023 _76024 _76025) (@lem5985523 B _76022 _76023 _76024 _76025)). Qed.
Lemma lem5985526 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) : term908 A B f g x op.
Proof. exact (conj (@lem5985404 A B x' f x op t g h1 h2) (@lem5985413 B op)). Qed.
Lemma lem5985528 {B : Type'} (_76022 : type1400 B) (_76023 : B) (_76024 : type1400 B) (_76025 : B) : term907 B _76022 _76023 _76024 _76025.
Proof. exact (EQ_MP (@lem5985524 B _76022 _76023 _76024 _76025) (@lem5985503 B _76023 _76025 _76022 _76024)). Qed.
Lemma lem5985529 {B : Type'} (_76022 : type1400 B) (_76023 : B) (_76024 : type1400 B) (_76025 : B) : term907 B _76022 _76023 _76024 _76025.
Proof. exact (@lem5985528 B _76022 _76023 _76024 _76025). Qed.
Lemma lem5985530 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) : term909 A B f op g x.
Proof. exact (@lem5985529 B op (@I (A -> B) f x) op (@I (A -> B) g x)). Qed.
Lemma lem5985533 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) : (term826 A B op f x) = (term826 A B op g x).
Proof. exact (@lem5985530 A B f op g x (@lem5985526 A B x' f x op t g h1 h2)). Qed.
Lemma lem5985534 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) : term910 A B f op g x.
Proof. exact (fun h0 : term911 A B f op g x => @lem5985533 A B x' f x op t g h1 h2). Qed.
Lemma lem5985536 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5985537 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (x : A) : (term910 A B f op g x) = ((term826 A B op f x) = (term826 A B op g x)).
Proof. exact (@lem5985536 ((term826 A B op f x) = (term826 A B op g x))). Qed.
Lemma lem5985538 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) : (term826 A B op f x) = (term826 A B op g x).
Proof. exact (EQ_MP (@lem5985537 A B f op g x) (@lem5985534 A B x' f x op t g h1 h2)). Qed.
Lemma lem5985556 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5985557 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : (term875 B _76032 _76033 _76034 _76035) = (term912 B _76033 _76035 _76032 _76034).
Proof. exact (@lem5985556 ((@I (B -> B) _76032 _76033) = (@I (B -> B) _76034 _76035)) (term913 B _76032 _76034)). Qed.
Lemma lem5985567 {B : Type'} (_76033 : B) (_76035 : B) : (term119 B _76033 _76035) = (term119 B _76033 _76035).
Proof. exact (eq_refl (term119 B _76033 _76035)). Qed.
Lemma lem5985568 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : (term877 B _76032 _76033 _76034 _76035) = (term914 B _76033 _76035 _76032 _76034).
Proof. exact (MK_COMB (@lem5985567 B _76033 _76035) (@lem5985557 B _76033 _76035 _76032 _76034)). Qed.
Lemma lem5985572 (q : Prop) (p : Prop) (r : Prop) : (term121 p q r) = (term121 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5985573 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : (term914 B _76033 _76035 _76032 _76034) = (term915 B _76033 _76035 _76032 _76034).
Proof. exact (@lem5985572 ((@I (B -> B) _76032 _76033) = (@I (B -> B) _76034 _76035)) (term118 B _76033 _76035) (term913 B _76032 _76034)). Qed.
Lemma lem5985595 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : (term877 B _76032 _76033 _76034 _76035) = (term915 B _76033 _76035 _76032 _76034).
Proof. exact (TRANS (@lem5985568 B _76033 _76035 _76032 _76034) (@lem5985573 B _76033 _76035 _76032 _76034)). Qed.
Lemma lem5985596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5985597 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : (term916 B _76032 _76033 _76034 _76035) = (term917 B _76033 _76035 _76032 _76034).
Proof. exact (MK_COMB (@lem5985596) (@lem5985595 B _76033 _76035 _76032 _76034)). Qed.
Lemma lem5985619 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : (term915 B _76033 _76035 _76032 _76034) = (term915 B _76033 _76035 _76032 _76034).
Proof. exact (eq_refl (term915 B _76033 _76035 _76032 _76034)). Qed.
Lemma lem5985620 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : ((term877 B _76032 _76033 _76034 _76035) = (term915 B _76033 _76035 _76032 _76034)) = ((term915 B _76033 _76035 _76032 _76034) = (term915 B _76033 _76035 _76032 _76034)).
Proof. exact (MK_COMB (@lem5985597 B _76033 _76035 _76032 _76034) (@lem5985619 B _76033 _76035 _76032 _76034)). Qed.
Lemma lem5985622 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5985623 (x : Prop) : (x = x) = True.
Proof. exact (@lem5985622 Prop x). Qed.
Lemma lem5985624 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : ((term915 B _76033 _76035 _76032 _76034) = (term915 B _76033 _76035 _76032 _76034)) = True.
Proof. exact (@lem5985623 (term915 B _76033 _76035 _76032 _76034)). Qed.
Lemma lem5985625 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : ((term877 B _76032 _76033 _76034 _76035) = (term915 B _76033 _76035 _76032 _76034)) = True.
Proof. exact (TRANS (@lem5985620 B _76033 _76035 _76032 _76034) (@lem5985624 B _76033 _76035 _76032 _76034)). Qed.
Lemma lem5985626 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : True = ((term877 B _76032 _76033 _76034 _76035) = (term915 B _76033 _76035 _76032 _76034)).
Proof. exact (SYM (@lem5985625 B _76033 _76035 _76032 _76034)). Qed.
Lemma lem5985627 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : (term877 B _76032 _76033 _76034 _76035) = (term915 B _76033 _76035 _76032 _76034).
Proof. exact (EQ_MP (@lem5985626 B _76033 _76035 _76032 _76034) (@lem0)). Qed.
Lemma lem5985628 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : term915 B _76033 _76035 _76032 _76034.
Proof. exact (EQ_MP (@lem5985627 B _76033 _76035 _76032 _76034) (@lem5985262 B _76032 _76033 _76034 _76035)). Qed.
Lemma lem5985630 (b : Prop) (a : Prop) : (a \/ b) = (term108 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5985631 {B : Type'} (_76032 : B -> B) (_76033 : B) (_76034 : B -> B) (_76035 : B) : (term915 B _76033 _76035 _76032 _76034) = (term918 B _76032 _76033 _76034 _76035).
Proof. exact (@lem5985630 (term919 B _76033 _76035 _76032 _76034) ((@I (B -> B) _76032 _76033) = (@I (B -> B) _76034 _76035))). Qed.
Lemma lem5985633 (a : Prop) (b : Prop) : (term127 a b) = (term128 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5985634 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : (term920 B _76033 _76035 _76032 _76034) = (term921 B _76033 _76035 _76032 _76034).
Proof. exact (@lem5985633 (term118 B _76033 _76035) (term913 B _76032 _76034)). Qed.
Lemma lem5985636 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5985637 {B : Type'} (_76033 : B) (_76035 : B) : (term131 B _76033 _76035) = (_76033 = _76035).
Proof. exact (@lem5985636 (_76033 = _76035)). Qed.
Lemma lem5985638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5985639 {B : Type'} (_76033 : B) (_76035 : B) : (term132 B _76033 _76035) = (term133 B _76033 _76035).
Proof. exact (MK_COMB (@lem5985638) (@lem5985637 B _76033 _76035)). Qed.
Lemma lem5985641 (a : Prop) : (term52 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5985642 {B : Type'} (_76032 : B -> B) (_76034 : B -> B) : (term922 B _76032 _76034) = (_76032 = _76034).
Proof. exact (@lem5985641 (_76032 = _76034)). Qed.
Lemma lem5985643 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : (term921 B _76033 _76035 _76032 _76034) = (term923 B _76033 _76035 _76032 _76034).
Proof. exact (MK_COMB (@lem5985639 B _76033 _76035) (@lem5985642 B _76032 _76034)). Qed.
Lemma lem5985644 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : (term920 B _76033 _76035 _76032 _76034) = (term923 B _76033 _76035 _76032 _76034).
Proof. exact (TRANS (@lem5985634 B _76033 _76035 _76032 _76034) (@lem5985643 B _76033 _76035 _76032 _76034)). Qed.
Lemma lem5985645 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5985646 {B : Type'} (_76033 : B) (_76035 : B) (_76032 : B -> B) (_76034 : B -> B) : (term924 B _76033 _76035 _76032 _76034) = (term925 B _76033 _76035 _76032 _76034).
Proof. exact (MK_COMB (@lem5985645) (@lem5985644 B _76033 _76035 _76032 _76034)). Qed.
Lemma lem5985647 {B : Type'} (_76032 : B -> B) (_76033 : B) (_76034 : B -> B) (_76035 : B) : ((@I (B -> B) _76032 _76033) = (@I (B -> B) _76034 _76035)) = ((@I (B -> B) _76032 _76033) = (@I (B -> B) _76034 _76035)).
Proof. exact (eq_refl ((@I (B -> B) _76032 _76033) = (@I (B -> B) _76034 _76035))). Qed.
Lemma lem5985648 {B : Type'} (_76032 : B -> B) (_76033 : B) (_76034 : B -> B) (_76035 : B) : (term918 B _76032 _76033 _76034 _76035) = (term926 B _76032 _76033 _76034 _76035).
Proof. exact (MK_COMB (@lem5985646 B _76033 _76035 _76032 _76034) (@lem5985647 B _76032 _76033 _76034 _76035)). Qed.
Lemma lem5985649 {B : Type'} (_76032 : B -> B) (_76033 : B) (_76034 : B -> B) (_76035 : B) : (term915 B _76033 _76035 _76032 _76034) = (term926 B _76032 _76033 _76034 _76035).
Proof. exact (TRANS (@lem5985631 B _76032 _76033 _76034 _76035) (@lem5985648 B _76032 _76033 _76034 _76035)). Qed.
Lemma lem5985651 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : term927 A B t f op g x.
Proof. exact (conj (@lem5985313 A B f op t g h3) (@lem5985538 A B x' f x op t g h1 h2)). Qed.
Lemma lem5985653 {B : Type'} (_76032 : B -> B) (_76033 : B) (_76034 : B -> B) (_76035 : B) : term926 B _76032 _76033 _76034 _76035.
Proof. exact (EQ_MP (@lem5985649 B _76032 _76033 _76034 _76035) (@lem5985628 B _76033 _76035 _76032 _76034)). Qed.
Lemma lem5985654 {B : Type'} (_76032 : B -> B) (_76033 : B) (_76034 : B -> B) (_76035 : B) : term926 B _76032 _76033 _76034 _76035.
Proof. exact (@lem5985653 B _76032 _76033 _76034 _76035). Qed.
Lemma lem5985655 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : term928 A B f x op t g.
Proof. exact (@lem5985654 B (term826 A B op f x) (@iterate B A op t f) (term826 A B op g x) (@iterate B A op t g)). Qed.
Lemma lem5985658 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : (term828 A B x op t f) = (term828 A B x op t g).
Proof. exact (@lem5985655 A B f x op t g (@lem5985651 A B x' x f op t g h1 h2 h3)). Qed.
Lemma lem5985659 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : term929 A B f x op t g.
Proof. exact (fun h0 : term830 A B f x op t g => @lem5985658 A B x' x f op t g h1 h2 h3). Qed.
Lemma lem5985661 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5985662 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term929 A B f x op t g) = ((term828 A B x op t f) = (term828 A B x op t g)).
Proof. exact (@lem5985661 ((term828 A B x op t f) = (term828 A B x op t g))). Qed.
Lemma lem5985663 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : (term828 A B x op t f) = (term828 A B x op t g).
Proof. exact (EQ_MP (@lem5985662 A B f x op t g) (@lem5985659 A B x' x f op t g h1 h2 h3)). Qed.
Lemma lem5985666 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5985668 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) : (term830 A B f x op t g) = (term930 A B f x op t g).
Proof. exact (@lem5985666 ((term828 A B x op t f) = (term828 A B x op t g))). Qed.
Lemma lem5985671 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term735 A B x' f x op t g) : term930 A B f x op t g.
Proof. exact (EQ_MP (@lem5985668 A B f x op t g) (@lem5984828 A B x' f x op t g h1)). Qed.
Lemma lem5985674 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : False.
Proof. exact (@lem5985671 A B x' f x op t g h2 (@lem5985663 A B x' x f op t g h1 h2 h3)). Qed.
Lemma lem5985675 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : term103.
Proof. exact (fun h0 : ~ False => @lem5985674 A B x' x f op t g h1 h2 h3). Qed.
Lemma lem5985677 (p : Prop) : (term101 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5985678 : term103 = False.
Proof. exact (@lem5985677 False). Qed.
Lemma lem5985679 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : False.
Proof. exact (EQ_MP (@lem5985678) (@lem5985675 A B x' x f op t g h1 h2 h3)). Qed.
Lemma lem5985680 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : ((@iterate B A op t f) = (@iterate B A op t g)) = False.
Proof. exact (prop_ext (fun h4 : (@iterate B A op t f) = (@iterate B A op t g) => @lem5985679 A B x' x f op t g h1 h2 h3) (fun h4 : False => @lem5984854 A B f op t g h3)). Qed.
Lemma lem5985681 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : False.
Proof. exact (EQ_MP (@lem5985680 A B x' x f op t g h1 h2 h3) (@lem5984854 A B f op t g h3)). Qed.
Lemma lem5985682 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : ((@iterate B A op t f) = (@iterate B A op t g)) = False.
Proof. exact (prop_ext (fun h4 : (@iterate B A op t f) = (@iterate B A op t g) => @lem5985681 A B x' x f op t g h1 h2 h3) (fun h4 : False => @lem5984674 A B f op t g h3)). Qed.
Lemma lem5985683 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : False.
Proof. exact (EQ_MP (@lem5985682 A B x' x f op t g h1 h2 h3) (@lem5984674 A B f op t g h3)). Qed.
Lemma lem5985684 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : ((@iterate B A op t f) = (@iterate B A op t g)) = False.
Proof. exact (prop_ext (fun h4 : (@iterate B A op t f) = (@iterate B A op t g) => @lem5985683 A B x' x f op t g h1 h2 h3) (fun h4 : False => @lem5984674 A B f op t g h3)). Qed.
Lemma lem5985685 {A B : Type'} (x' : A) (x : A) (f : A -> B) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) (h3 : (@iterate B A op t f) = (@iterate B A op t g)) : False.
Proof. exact (EQ_MP (@lem5985684 A B x' x f op t g h1 h2 h3) (@lem5984674 A B f op t g h3)). Qed.
Lemma lem5985686 {A B : Type'} (x' : A) (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term735 A B x' f x op t g) : False.
Proof. exact (or_elim (@lem5984386 A B x' f x op t g h2) (fun h0 : term837 A B t f g x' => @lem5985145 A B x op t f g x' h1 h2 h0) (fun h0 : (@iterate B A op t f) = (@iterate B A op t g) => @lem5985685 A B x' x f op t g h1 h2 h0)). Qed.
Lemma lem5985687 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (t : A -> Prop) (g : A -> B) (h1 : term608 A) (h2 : term738 A B f x op t g) : False.
Proof. exact (ex_elim (@lem5984051 A B f x op t g h2) (fun x' : A => fun h0 : term737 A B f x op t g x' => @lem5985686 A B x' f x op t g h1 h0)). Qed.
Lemma lem5985688 {A B : Type'} (f : A -> B) (x : A) (op : type1400 B) (g : A -> B) (h1 : term608 A) (h2 : term740 A B f x op g) : False.
Proof. exact (ex_elim (@lem5984050 A B f x op g h2) (fun t : A -> Prop => fun h0 : term739 A B f x op g t => @lem5985687 A B f x op t g h1 h0)). Qed.
Lemma lem5985689 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term608 A) (h2 : term607 A B f op g) : False.
Proof. exact (ex_elim (@lem5983155 A B f op g h2) (fun x : A => fun h0 : term741 A B f op g x => @lem5985688 A B f x op g h1 h0)). Qed.
Lemma lem5985690 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term608 A) (h2 : term607 A B f op g) : term613 B.
Proof. exact (fun h0 : term608 B => @lem5985689 A B f op g h1 h2). Qed.
Lemma lem5985691 {B : Type'} : (term613 B) = (term614 B).
Proof. exact (@lem69 (term608 B)). Qed.
Lemma lem5985692 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term608 A) (h2 : term607 A B f op g) : term614 B.
Proof. exact (EQ_MP (@lem5985691 B) (@lem5985690 A B f op g h1 h2)). Qed.
Lemma lem5985693 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term607 A B f op g) : term617 A B.
Proof. exact (fun h0 : term608 A => @lem5985692 A B f op g h0 h1). Qed.
Lemma lem5985694 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : term619 A B f op g.
Proof. exact (fun h0 : term607 A B f op g => @lem5985693 A B f op g h0). Qed.
Lemma lem5985699 {A B : Type'} (op : type1400 B) (g : A -> B) : term623 A B op g.
Proof. exact (fun f : A -> B => @lem5985694 A B f op g). Qed.
Lemma lem5985704 {A B : Type'} (g : A -> B) : term627 A B g.
Proof. exact (fun op : type1400 B => @lem5985699 A B op g). Qed.
Lemma lem5985709 {A B : Type'} : term631 A B.
Proof. exact (fun g : A -> B => @lem5985704 A B g). Qed.
Lemma lem5985710 {A B : Type'} : term630 A B.
Proof. exact (EQ_MP (@lem5982840 A B) (@lem5985709 A B)). Qed.
Lemma lem5985711 {A B : Type'} (g : A -> B) : term931 A B g.
Proof. exact (@lem5985710 A B g). Qed.
Lemma lem5985712 {A B : Type'} (g : A -> B) : (term931 A B g) = (term626 A B g).
Proof. exact (eq_refl (term931 A B g)). Qed.
Lemma lem5985713 {A B : Type'} (g : A -> B) : term626 A B g.
Proof. exact (EQ_MP (@lem5985712 A B g) (@lem5985711 A B g)). Qed.
Lemma lem5985714 {A B : Type'} (g : A -> B) (op : type1400 B) : term932 A B g op.
Proof. exact (@lem5985713 A B g op). Qed.
Lemma lem5985715 {A B : Type'} (op : type1400 B) (g : A -> B) : (term932 A B g op) = (term622 A B op g).
Proof. exact (eq_refl (term932 A B g op)). Qed.
Lemma lem5985716 {A B : Type'} (op : type1400 B) (g : A -> B) : term622 A B op g.
Proof. exact (EQ_MP (@lem5985715 A B op g) (@lem5985714 A B g op)). Qed.
Lemma lem5985717 {A B : Type'} (op : type1400 B) (g : A -> B) (f : A -> B) : term933 A B op g f.
Proof. exact (@lem5985716 A B op g f). Qed.
Lemma lem5985718 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : (term933 A B op g f) = (term609 A B f op g).
Proof. exact (eq_refl (term933 A B op g f)). Qed.
Lemma lem5985719 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : term609 A B f op g.
Proof. exact (EQ_MP (@lem5985718 A B f op g) (@lem5985717 A B op g f)). Qed.
Lemma lem5985721 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : term609 A B f op g.
Proof. exact (@lem5982528 A B f op g (@lem5985719 A B f op g)). Qed.
Lemma lem5985722 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term607 A B f op g) : term616 A B.
Proof. exact (@lem5985721 A B f op g (@lem5982509 A B f op g h1)). Qed.
Lemma lem5985723 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term607 A B f op g) : term613 B.
Proof. exact (@lem5985722 A B f op g h1 (@lem5982510 A)). Qed.
Lemma lem5985724 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term607 A B f op g) : False.
Proof. exact (@lem5985723 A B f op g h1 (@lem5982512 B)). Qed.
Lemma lem5985725 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term607 A B f op g) : (term607 A B f op g) = False.
Proof. exact (prop_ext (fun h2 : term607 A B f op g => @lem5985724 A B f op g h1) (fun h2 : False => @lem5982509 A B f op g h1)). Qed.
Lemma lem5985726 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) (h1 : term607 A B f op g) : False.
Proof. exact (EQ_MP (@lem5985725 A B f op g h1) (@lem5982509 A B f op g h1)). Qed.
Lemma lem5985727 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : term606 A B f op g.
Proof. exact (fun h0 : term607 A B f op g => @lem5985726 A B f op g h0). Qed.
Lemma lem5985728 {A B : Type'} (f : A -> B) (op : type1400 B) (g : A -> B) : term604 A B f op g.
Proof. exact (EQ_MP (@lem5982508 A B f op g) (@lem5985727 A B f op g)). Qed.
Lemma lem5985729 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term508 A B f op g.
Proof. exact (EQ_MP (@lem5982504 A B f g op h1) (@lem5985728 A B f op g)). Qed.
Lemma lem5985730 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term517 A B f op g.
Proof. exact (@lem5976657 A B f op g (@lem5985729 A B f g op h1)). Qed.
Lemma lem5985731 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term934 A B g op f s.
Proof. exact (@lem5985730 A B f g op h1 (@support A B op f s)). Qed.
Lemma lem5985732 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (g : A -> B) : (term934 A B g op f s) = (term479 A B op f s g).
Proof. exact (eq_refl (term934 A B g op f s)). Qed.
Lemma lem5985733 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term479 A B op f s g.
Proof. exact (EQ_MP (@lem5985732 A B op f s g) (@lem5985731 A B g f s op h1)). Qed.
Lemma lem5985734 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term478 A B op f s g.
Proof. exact (EQ_MP (@lem5976624 A B op f s g) (@lem5985733 A B f s g op h1)). Qed.
Lemma lem5985735 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : @monoidal B op) (h2 : term188 A B op s f g) : (term156 A B op s f) = (term185 A B op f s g).
Proof. exact (@lem5985734 A B f s g op h1 (@lem5971743 A B op s f g h2)). Qed.
Lemma lem5985736 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) : (term188 A B op s f g) = ((term156 A B op s f) = (term185 A B op f s g)).
Proof. exact (prop_ext (fun h4 : term188 A B op s f g => @lem5985735 A B op s f g h3 h4) (fun h4 : (term156 A B op s f) = (term185 A B op f s g) => @lem5976606 A B g f s op h1 h2 h3)). Qed.
Lemma lem5985737 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) : (term156 A B op s f) = (term185 A B op f s g).
Proof. exact (EQ_MP (@lem5985736 A B g f s op h1 h2 h3) (@lem5976606 A B g f s op h1 h2 h3)). Qed.
Lemma lem5985738 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) : (term156 A B op s f) = (term174 A B f s g op).
Proof. exact (EQ_MP (@lem5971718 A B f s g op) (@lem5985737 A B g f s op h1 h2 h3)). Qed.
Lemma lem5985739 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term177 A B op f s) : (@neutral B op) = (term33 A B f s g op).
Proof. exact (EQ_MP (@lem5971698 A B g op f s h1) (@lem5971742 A B f s g op)). Qed.
Lemma lem5985740 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term177 A B op f s) : (term177 A B op f s) = ((@neutral B op) = (term33 A B f s g op)).
Proof. exact (prop_ext (fun h2 : term177 A B op f s => @lem5985739 A B g op f s h1) (fun h2 : (@neutral B op) = (term33 A B f s g op) => @lem5971683 A B op f s h1)). Qed.
Lemma lem5985741 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term177 A B op f s) : (@neutral B op) = (term33 A B f s g op).
Proof. exact (EQ_MP (@lem5985740 A B g op f s h1) (@lem5971683 A B op f s h1)). Qed.
Lemma lem5985742 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) : term161 A B f s g op.
Proof. exact (fun h0 : term177 A B op f s => @lem5985741 A B g op f s h0). Qed.
Lemma lem5985743 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) : (term156 A B op s f) = (term33 A B f s g op).
Proof. exact (EQ_MP (@lem5971682 A B g op f s h2) (@lem5985738 A B g f s op h1 h2 h3)). Qed.
Lemma lem5985744 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) : (term157 A B op f s) = ((term156 A B op s f) = (term33 A B f s g op)).
Proof. exact (prop_ext (fun h4 : term157 A B op f s => @lem5985743 A B g f s op h1 h2 h3) (fun h4 : (term156 A B op s f) = (term33 A B f s g op) => @lem5971667 A B op f s h2)). Qed.
Lemma lem5985745 {A B : Type'} (g : A -> B) (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : term26 A B s f g) (h2 : term157 A B op f s) (h3 : @monoidal B op) : (term156 A B op s f) = (term33 A B f s g op).
Proof. exact (EQ_MP (@lem5985744 A B g f s op h1 h2 h3) (@lem5971667 A B op f s h2)). Qed.
Lemma lem5985746 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : term165 A B f s g op.
Proof. exact (fun h0 : term157 A B op f s => @lem5985745 A B g f s op h1 h0 h2). Qed.
Lemma lem5985747 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : term168 A B f s g op.
Proof. exact (conj (@lem5985746 A B s f g op h1 h2) (@lem5985742 A B f s g op)). Qed.
Lemma lem5985748 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : (term27 A B s f op) = (term33 A B f s g op).
Proof. exact (EQ_MP (@lem5971666 A B f s g op) (@lem5985747 A B s f g op h1 h2)). Qed.
Lemma lem5985749 {A B : Type'} (g : A -> B) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term26 A B s f g) (h2 : @monoidal B op) (h3 : (@support A B op g s) = (@support A B op f s)) : (term27 A B s f op) = (term27 A B s g op).
Proof. exact (EQ_MP (@lem5970144 A B g op f s h3) (@lem5985748 A B s f g op h1 h2)). Qed.
Lemma lem5985750 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : ((@support A B op g s) = (@support A B op f s)) = ((term27 A B s f op) = (term27 A B s g op)).
Proof. exact (prop_ext (fun h3 : (@support A B op g s) = (@support A B op f s) => @lem5985749 A B g op f s h1 h2 h3) (fun h3 : (term27 A B s f op) = (term27 A B s g op) => @lem5971648 A B s f g op h1 h2)). Qed.
Lemma lem5985751 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : (term27 A B s f op) = (term27 A B s g op).
Proof. exact (EQ_MP (@lem5985750 A B s f g op h1 h2) (@lem5971648 A B s f g op h1 h2)). Qed.
Lemma lem5985752 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : (@iterate B A op s f) = (@iterate B A op s g).
Proof. exact (EQ_MP (@lem5970130 A B f op s g) (@lem5985751 A B s f g op h1 h2)). Qed.
Lemma lem5985753 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : (term26 A B s f g) = ((@iterate B A op s f) = (@iterate B A op s g)).
Proof. exact (prop_ext (fun h3 : term26 A B s f g => @lem5985752 A B s f g op h1 h2) (fun h3 : (@iterate B A op s f) = (@iterate B A op s g) => @lem5970117 A B s f g h1)). Qed.
Lemma lem5985754 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : term26 A B s f g) (h2 : @monoidal B op) : (@iterate B A op s f) = (@iterate B A op s g).
Proof. exact (EQ_MP (@lem5985753 A B s f g op h1 h2) (@lem5970117 A B s f g h1)). Qed.
Lemma lem5985755 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term487 A B f op s g.
Proof. exact (fun h0 : term26 A B s f g => @lem5985754 A B s f g op h0 h1). Qed.
Lemma lem5985760 {A B : Type'} (f : A -> B) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term935 A B f op g.
Proof. exact (fun s : A -> Prop => @lem5985755 A B f s g op h1). Qed.
Lemma lem5985765 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term936 A B f op.
Proof. exact (fun g : A -> B => @lem5985760 A B f g op h1). Qed.
Lemma lem5985770 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term937 A B op.
Proof. exact (fun f : A -> B => @lem5985765 A B f op h1). Qed.
Lemma lem5985771 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = (term937 A B op).
Proof. exact (prop_ext (fun h2 : @monoidal B op => @lem5985770 A B op h1) (fun h2 : term937 A B op => @lem5970116 B op h1)). Qed.
Lemma lem5985772 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term937 A B op.
Proof. exact (EQ_MP (@lem5985771 A B op h1) (@lem5970116 B op h1)). Qed.
Lemma lem5985773 {A B : Type'} (op : type1400 B) : term938 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem5985772 A B op h0). Qed.
Lemma lem5985778 {A B : Type'} : term939 A B.
Proof. exact (fun op : type1400 B => @lem5985773 A B op). Qed.

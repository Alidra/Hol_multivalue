Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3192217_term_abbrevs.
Require Import EXTENSION_spec.
Require Import INSERT_DEF_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184704_spec.
Require Import thm3184707_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem3192080 {_83169 : Type'} : term0 _83169.
Proof. exact (EQ_MP (@lem3184707 _83169) (@lem3184704 _83169)). Qed.
Lemma lem3192081 {_83169 : Type'} (p : _83169 -> Prop) : term1 _83169 p.
Proof. exact (@lem3192080 _83169 p). Qed.
Lemma lem3192082 {_83169 : Type'} (p : _83169 -> Prop) : (term1 _83169 p) = (term2 _83169 p).
Proof. exact (eq_refl (term1 _83169 p)). Qed.
Lemma lem3192083 {_83169 : Type'} (p : _83169 -> Prop) : term2 _83169 p.
Proof. exact (EQ_MP (@lem3192082 _83169 p) (@lem3192081 _83169 p)). Qed.
Lemma lem3192084 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : term3 _83169 p x.
Proof. exact (@lem3192083 _83169 p x). Qed.
Lemma lem3192085 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : (term3 _83169 p x) = ((term4 _83169 x p) = (p x)).
Proof. exact (eq_refl (term3 _83169 p x)). Qed.
Lemma lem3192101 {_83095 : Type'} : term5 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3192102 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (@lem3192101 _83095 p). Qed.
Lemma lem3192103 {_83095 : Type'} (p : _83095 -> Prop) : (term6 _83095 p) = (term7 _83095 p).
Proof. exact (eq_refl (term6 _83095 p)). Qed.
Lemma lem3192104 {_83095 : Type'} (p : _83095 -> Prop) : term7 _83095 p.
Proof. exact (EQ_MP (@lem3192103 _83095 p) (@lem3192102 _83095 p)). Qed.
Lemma lem3192105 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term8 _83095 p x.
Proof. exact (@lem3192104 _83095 p x). Qed.
Lemma lem3192106 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 p x) = ((term9 _83095 x p) = (p x)).
Proof. exact (eq_refl (term8 _83095 p x)). Qed.
Lemma lem3192115 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem3186538 A s). Qed.
Lemma lem3192116 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (eq_refl (term10 A s)). Qed.
Lemma lem3192117 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (EQ_MP (@lem3192116 A s) (@lem3192115 A s)). Qed.
Lemma lem3192118 {A : Type'} (s : A -> Prop) (x : A) : term12 A s x.
Proof. exact (@lem3192117 A s x). Qed.
Lemma lem3192119 {A : Type'} (s : A -> Prop) (x : A) : (term12 A s x) = ((@INSERT A x s) = (term13 A s x)).
Proof. exact (eq_refl (term12 A s x)). Qed.
Lemma lem3192121 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3192122 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem3192123 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem3192122 A s) (@lem3192121 A s)). Qed.
Lemma lem3192124 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem3192123 A s t). Qed.
Lemma lem3192125 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem3192130 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3192125 A s t) (@lem3192124 A s t)). Qed.
Lemma lem3192131 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (@lem3192130 A s t). Qed.
Lemma lem3192132 {A : Type'} (s : A -> Prop) (x : A) : ((@INSERT A x s) = (term18 A s x)) = (term19 A s x).
Proof. exact (@lem3192131 A (@INSERT A x s) (term18 A s x)). Qed.
Lemma lem3192142 {A : Type'} (s : A -> Prop) (x : A) : (@INSERT A x s) = (term13 A s x).
Proof. exact (EQ_MP (@lem3192119 A s x) (@lem3192118 A s x)). Qed.
Lemma lem3192143 {A : Type'} (s : A -> Prop) (x : A) : (@INSERT A x s) = (term13 A s x).
Proof. exact (@lem3192142 A s x). Qed.
Lemma lem3192150 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem3192151 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term20 A x' x s) = (term21 A x' s x).
Proof. exact (MK_COMB (@lem3192150 A x') (@lem3192143 A s x)). Qed.
Lemma lem3192153 {_83169 : Type'} (p : _83169 -> Prop) (x : _83169) : (term4 _83169 x p) = (p x).
Proof. exact (EQ_MP (@lem3192085 _83169 p x) (@lem3192084 _83169 p x)). Qed.
Lemma lem3192154 {A : Type'} (p : A -> Prop) (x : A) : (term4 A x p) = (p x).
Proof. exact (@lem3192153 A p x). Qed.
Lemma lem3192155 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term22 A x' s x) = (term23 A s x x').
Proof. exact (@lem3192154 A (term13 A s x) x'). Qed.
Lemma lem3192156 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term23 A s x y) = (term24 A s y x).
Proof. exact (eq_refl (term23 A s x y)). Qed.
Lemma lem3192157 {A : Type'} (s : A -> Prop) (x : A) : (term25 A s x) = (term13 A s x).
Proof. exact (fun_ext (fun y : A => @lem3192156 A s y x)). Qed.
Lemma lem3192158 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem3192159 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term22 A x' s x) = (term21 A x' s x).
Proof. exact (MK_COMB (@lem3192158 A x') (@lem3192157 A s x)). Qed.
Lemma lem3192160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3192161 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term26 A x' s x) = (term27 A x' s x).
Proof. exact (MK_COMB (@lem3192160) (@lem3192159 A x' s x)). Qed.
Lemma lem3192162 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term23 A s x x') = (term24 A s x' x).
Proof. exact (eq_refl (term23 A s x x')). Qed.
Lemma lem3192163 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((term22 A x' s x) = (term23 A s x x')) = ((term21 A x' s x) = (term24 A s x' x)).
Proof. exact (MK_COMB (@lem3192161 A x' s x) (@lem3192162 A s x' x)). Qed.
Lemma lem3192164 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term21 A x' s x) = (term24 A s x' x).
Proof. exact (EQ_MP (@lem3192163 A s x' x) (@lem3192155 A s x x')). Qed.
Lemma lem3192171 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term20 A x' x s) = (term24 A s x' x).
Proof. exact (TRANS (@lem3192151 A x' s x) (@lem3192164 A s x' x)). Qed.
Lemma lem3192172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3192173 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term28 A x' x s) = (term29 A s x' x).
Proof. exact (MK_COMB (@lem3192172) (@lem3192171 A s x' x)). Qed.
Lemma lem3192175 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term9 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3192106 _83095 p x) (@lem3192105 _83095 p x)). Qed.
Lemma lem3192176 {A : Type'} (p : A -> Prop) (x : A) : (term9 A x p) = (p x).
Proof. exact (@lem3192175 A p x). Qed.
Lemma lem3192177 {A : Type'} (s : A -> Prop) (x : A) (x' : A) : (term30 A x' s x) = (term23 A s x x').
Proof. exact (@lem3192176 A (term13 A s x) x'). Qed.
Lemma lem3192178 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term23 A s x y) = (term24 A s y x).
Proof. exact (eq_refl (term23 A s x y)). Qed.
Lemma lem3192179 {A : Type'} (GEN_PVAR_5 : A) : (@SETSPEC A GEN_PVAR_5) = (@SETSPEC A GEN_PVAR_5).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_5)). Qed.
Lemma lem3192180 {A : Type'} (GEN_PVAR_5 : A) (s : A -> Prop) (y : A) (x : A) : (term31 A GEN_PVAR_5 s x y) = (term32 A GEN_PVAR_5 s y x).
Proof. exact (MK_COMB (@lem3192179 A GEN_PVAR_5) (@lem3192178 A s y x)). Qed.
Lemma lem3192181 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3192182 {A : Type'} (GEN_PVAR_5 : A) (s : A -> Prop) (x : A) (y : A) : (term33 A GEN_PVAR_5 s x y) = (term34 A GEN_PVAR_5 s x y).
Proof. exact (MK_COMB (@lem3192180 A GEN_PVAR_5 s y x) (@lem3192181 A y)). Qed.
Lemma lem3192183 {A : Type'} (GEN_PVAR_5 : A) (s : A -> Prop) (x : A) : (term35 A GEN_PVAR_5 s x) = (term36 A GEN_PVAR_5 s x).
Proof. exact (fun_ext (fun y : A => @lem3192182 A GEN_PVAR_5 s x y)). Qed.
Lemma lem3192184 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3192185 {A : Type'} (GEN_PVAR_5 : A) (s : A -> Prop) (x : A) : (term37 A GEN_PVAR_5 s x) = (term38 A GEN_PVAR_5 s x).
Proof. exact (MK_COMB (@lem3192184 A) (@lem3192183 A GEN_PVAR_5 s x)). Qed.
Lemma lem3192186 {A : Type'} (s : A -> Prop) (x : A) : (term39 A s x) = (term40 A s x).
Proof. exact (fun_ext (fun GEN_PVAR_5 : A => @lem3192185 A GEN_PVAR_5 s x)). Qed.
Lemma lem3192187 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3192188 {A : Type'} (s : A -> Prop) (x : A) : (term41 A s x) = (term18 A s x).
Proof. exact (MK_COMB (@lem3192187 A) (@lem3192186 A s x)). Qed.
Lemma lem3192189 {A : Type'} (x' : A) : (@IN A x') = (@IN A x').
Proof. exact (eq_refl (@IN A x')). Qed.
Lemma lem3192190 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term30 A x' s x) = (term42 A x' s x).
Proof. exact (MK_COMB (@lem3192189 A x') (@lem3192188 A s x)). Qed.
Lemma lem3192191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3192192 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term43 A x' s x) = (term44 A x' s x).
Proof. exact (MK_COMB (@lem3192191) (@lem3192190 A x' s x)). Qed.
Lemma lem3192193 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term23 A s x x') = (term24 A s x' x).
Proof. exact (eq_refl (term23 A s x x')). Qed.
Lemma lem3192194 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((term30 A x' s x) = (term23 A s x x')) = ((term42 A x' s x) = (term24 A s x' x)).
Proof. exact (MK_COMB (@lem3192192 A x' s x) (@lem3192193 A s x' x)). Qed.
Lemma lem3192195 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term42 A x' s x) = (term24 A s x' x).
Proof. exact (EQ_MP (@lem3192194 A s x' x) (@lem3192177 A s x x')). Qed.
Lemma lem3192202 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((term20 A x' x s) = (term42 A x' s x)) = ((term24 A s x' x) = (term24 A s x' x)).
Proof. exact (MK_COMB (@lem3192173 A s x' x) (@lem3192195 A s x' x)). Qed.
Lemma lem3192204 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3192205 (x : Prop) : (x = x) = True.
Proof. exact (@lem3192204 Prop x). Qed.
Lemma lem3192206 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((term24 A s x' x) = (term24 A s x' x)) = True.
Proof. exact (@lem3192205 (term24 A s x' x)). Qed.
Lemma lem3192207 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term20 A x' x s) = (term42 A x' s x)) = True.
Proof. exact (TRANS (@lem3192202 A s x' x) (@lem3192206 A s x' x)). Qed.
Lemma lem3192208 {A : Type'} (s : A -> Prop) (x : A) : (term45 A s x) = (term46 A).
Proof. exact (fun_ext (fun x' : A => @lem3192207 A x' s x)). Qed.
Lemma lem3192209 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3192210 {A : Type'} (s : A -> Prop) (x : A) : (term19 A s x) = (term47 A).
Proof. exact (MK_COMB (@lem3192209 A) (@lem3192208 A s x)). Qed.
Lemma lem3192212 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3192213 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (@lem3192212 A t). Qed.
Lemma lem3192214 {A : Type'} : (term47 A) = True.
Proof. exact (@lem3192213 A True). Qed.
Lemma lem3192215 {A : Type'} (s : A -> Prop) (x : A) : (term19 A s x) = True.
Proof. exact (TRANS (@lem3192210 A s x) (@lem3192214 A)). Qed.
Lemma lem3192216 {A : Type'} (s : A -> Prop) (x : A) : ((@INSERT A x s) = (term18 A s x)) = True.
Proof. exact (TRANS (@lem3192132 A s x) (@lem3192215 A s x)). Qed.
Lemma lem3192217 {A : Type'} (s : A -> Prop) (x : A) : True = ((@INSERT A x s) = (term18 A s x)).
Proof. exact (SYM (@lem3192216 A s x)). Qed.

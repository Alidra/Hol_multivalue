Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_SUPPORT_term_abbrevs.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem5718074 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5718075 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem5718074 _83095 p). Qed.
Lemma lem5718076 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem5718077 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem5718076 _83095 p) (@lem5718075 _83095 p)). Qed.
Lemma lem5718078 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem5718077 _83095 p x). Qed.
Lemma lem5718079 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem5718088 {A B : Type'} (s : A -> Prop) : term5 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem5718089 {A B : Type'} (s : A -> Prop) : (term5 A B s) = (term6 A B s).
Proof. exact (eq_refl (term5 A B s)). Qed.
Lemma lem5718090 {A B : Type'} (s : A -> Prop) : term6 A B s.
Proof. exact (EQ_MP (@lem5718089 A B s) (@lem5718088 A B s)). Qed.
Lemma lem5718091 {A B : Type'} (s : A -> Prop) (f : A -> B) : term7 A B s f.
Proof. exact (@lem5718090 A B s f). Qed.
Lemma lem5718092 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term7 A B s f) = (term8 A B s f).
Proof. exact (eq_refl (term7 A B s f)). Qed.
Lemma lem5718093 {A B : Type'} (s : A -> Prop) (f : A -> B) : term8 A B s f.
Proof. exact (EQ_MP (@lem5718092 A B s f) (@lem5718091 A B s f)). Qed.
Lemma lem5718094 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term9 A B s f op.
Proof. exact (@lem5718093 A B s f op). Qed.
Lemma lem5718095 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term9 A B s f op) = ((@support A B op f s) = (term10 A B s f op)).
Proof. exact (eq_refl (term9 A B s f op)). Qed.
Lemma lem5718116 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term10 A B s f op).
Proof. exact (EQ_MP (@lem5718095 A B s f op) (@lem5718094 A B s f op)). Qed.
Lemma lem5718117 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (op : type1400 _119826) : (@support _119829 _119826 op f s) = (term11 _119826 _119829 s f op).
Proof. exact (@lem5718116 _119829 _119826 s f op). Qed.
Lemma lem5718126 {_119829 : Type'} (x : _119829) : (@IN _119829 x) = (@IN _119829 x).
Proof. exact (eq_refl (@IN _119829 x)). Qed.
Lemma lem5718127 {_119826 _119829 : Type'} (x : _119829) (s : _119829 -> Prop) (f : _119829 -> _119826) (op : type1400 _119826) : (term12 _119826 _119829 x op f s) = (term13 _119826 _119829 x s f op).
Proof. exact (MK_COMB (@lem5718126 _119829 x) (@lem5718117 _119826 _119829 s f op)). Qed.
Lemma lem5718129 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5718079 _83095 p x) (@lem5718078 _83095 p x)). Qed.
Lemma lem5718130 {_119829 : Type'} (p : _119829 -> Prop) (x : _119829) : (term4 _119829 x p) = (p x).
Proof. exact (@lem5718129 _119829 p x). Qed.
Lemma lem5718131 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (op : type1400 _119826) (x : _119829) : (term14 _119826 _119829 x s f op) = (term15 _119826 _119829 s f op x).
Proof. exact (@lem5718130 _119829 (term16 _119826 _119829 s f op) x). Qed.
Lemma lem5718132 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term15 _119826 _119829 s f op x) = (term17 _119826 _119829 s f x op).
Proof. exact (eq_refl (term15 _119826 _119829 s f op x)). Qed.
Lemma lem5718133 {_119829 : Type'} (GEN_PVAR_237 : _119829) : (@SETSPEC _119829 GEN_PVAR_237) = (@SETSPEC _119829 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _119829 GEN_PVAR_237)). Qed.
Lemma lem5718134 {_119826 _119829 : Type'} (GEN_PVAR_237 : _119829) (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term18 _119826 _119829 GEN_PVAR_237 s f op x) = (term19 _119826 _119829 GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem5718133 _119829 GEN_PVAR_237) (@lem5718132 _119826 _119829 s f x op)). Qed.
Lemma lem5718135 {_119829 : Type'} (x : _119829) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5718136 {_119826 _119829 : Type'} (GEN_PVAR_237 : _119829) (s : _119829 -> Prop) (f : _119829 -> _119826) (op : type1400 _119826) (x : _119829) : (term20 _119826 _119829 GEN_PVAR_237 s f op x) = (term21 _119826 _119829 GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem5718134 _119826 _119829 GEN_PVAR_237 s f x op) (@lem5718135 _119829 x)). Qed.
Lemma lem5718137 {_119826 _119829 : Type'} (GEN_PVAR_237 : _119829) (s : _119829 -> Prop) (f : _119829 -> _119826) (op : type1400 _119826) : (term22 _119826 _119829 GEN_PVAR_237 s f op) = (term23 _119826 _119829 GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : _119829 => @lem5718136 _119826 _119829 GEN_PVAR_237 s f op x)). Qed.
Lemma lem5718138 {_119829 : Type'} : (@ex _119829) = (@ex _119829).
Proof. exact (eq_refl (@ex _119829)). Qed.
Lemma lem5718139 {_119826 _119829 : Type'} (GEN_PVAR_237 : _119829) (s : _119829 -> Prop) (f : _119829 -> _119826) (op : type1400 _119826) : (term24 _119826 _119829 GEN_PVAR_237 s f op) = (term25 _119826 _119829 GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem5718138 _119829) (@lem5718137 _119826 _119829 GEN_PVAR_237 s f op)). Qed.
Lemma lem5718140 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (op : type1400 _119826) : (term26 _119826 _119829 s f op) = (term27 _119826 _119829 s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _119829 => @lem5718139 _119826 _119829 GEN_PVAR_237 s f op)). Qed.
Lemma lem5718141 {_119829 : Type'} : (@GSPEC _119829) = (@GSPEC _119829).
Proof. exact (eq_refl (@GSPEC _119829)). Qed.
Lemma lem5718142 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (op : type1400 _119826) : (term28 _119826 _119829 s f op) = (term11 _119826 _119829 s f op).
Proof. exact (MK_COMB (@lem5718141 _119829) (@lem5718140 _119826 _119829 s f op)). Qed.
Lemma lem5718143 {_119829 : Type'} (x : _119829) : (@IN _119829 x) = (@IN _119829 x).
Proof. exact (eq_refl (@IN _119829 x)). Qed.
Lemma lem5718144 {_119826 _119829 : Type'} (x : _119829) (s : _119829 -> Prop) (f : _119829 -> _119826) (op : type1400 _119826) : (term14 _119826 _119829 x s f op) = (term13 _119826 _119829 x s f op).
Proof. exact (MK_COMB (@lem5718143 _119829 x) (@lem5718142 _119826 _119829 s f op)). Qed.
Lemma lem5718145 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5718146 {_119826 _119829 : Type'} (x : _119829) (s : _119829 -> Prop) (f : _119829 -> _119826) (op : type1400 _119826) : (term29 _119826 _119829 x s f op) = (term30 _119826 _119829 x s f op).
Proof. exact (MK_COMB (@lem5718145) (@lem5718144 _119826 _119829 x s f op)). Qed.
Lemma lem5718147 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term15 _119826 _119829 s f op x) = (term17 _119826 _119829 s f x op).
Proof. exact (eq_refl (term15 _119826 _119829 s f op x)). Qed.
Lemma lem5718148 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : ((term14 _119826 _119829 x s f op) = (term15 _119826 _119829 s f op x)) = ((term13 _119826 _119829 x s f op) = (term17 _119826 _119829 s f x op)).
Proof. exact (MK_COMB (@lem5718146 _119826 _119829 x s f op) (@lem5718147 _119826 _119829 s f x op)). Qed.
Lemma lem5718149 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term13 _119826 _119829 x s f op) = (term17 _119826 _119829 s f x op).
Proof. exact (EQ_MP (@lem5718148 _119826 _119829 s f x op) (@lem5718131 _119826 _119829 s f op x)). Qed.
Lemma lem5718154 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term12 _119826 _119829 x op f s) = (term17 _119826 _119829 s f x op).
Proof. exact (TRANS (@lem5718127 _119826 _119829 x s f op) (@lem5718149 _119826 _119829 s f x op)). Qed.
Lemma lem5718155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5718156 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term31 _119826 _119829 x op f s) = (term32 _119826 _119829 s f x op).
Proof. exact (MK_COMB (@lem5718155) (@lem5718154 _119826 _119829 s f x op)). Qed.
Lemma lem5718161 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term17 _119826 _119829 s f x op) = (term17 _119826 _119829 s f x op).
Proof. exact (eq_refl (term17 _119826 _119829 s f x op)). Qed.
Lemma lem5718162 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : ((term12 _119826 _119829 x op f s) = (term17 _119826 _119829 s f x op)) = ((term17 _119826 _119829 s f x op) = (term17 _119826 _119829 s f x op)).
Proof. exact (MK_COMB (@lem5718156 _119826 _119829 s f x op) (@lem5718161 _119826 _119829 s f x op)). Qed.
Lemma lem5718164 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5718165 (x : Prop) : (x = x) = True.
Proof. exact (@lem5718164 Prop x). Qed.
Lemma lem5718166 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : ((term17 _119826 _119829 s f x op) = (term17 _119826 _119829 s f x op)) = True.
Proof. exact (@lem5718165 (term17 _119826 _119829 s f x op)). Qed.
Lemma lem5718167 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : ((term12 _119826 _119829 x op f s) = (term17 _119826 _119829 s f x op)) = True.
Proof. exact (TRANS (@lem5718162 _119826 _119829 s f x op) (@lem5718166 _119826 _119829 s f x op)). Qed.
Lemma lem5718168 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term33 _119826 _119829 f x op) = (term34 _119829).
Proof. exact (fun_ext (fun s : _119829 -> Prop => @lem5718167 _119826 _119829 s f x op)). Qed.
Lemma lem5718169 {_119829 : Type'} : (@all (_119829 -> Prop)) = (@all (_119829 -> Prop)).
Proof. exact (eq_refl (@all (_119829 -> Prop))). Qed.
Lemma lem5718170 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term35 _119826 _119829 f x op) = (term36 _119829).
Proof. exact (MK_COMB (@lem5718169 _119829) (@lem5718168 _119826 _119829 f x op)). Qed.
Lemma lem5718172 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5718173 {_119829 : Type'} (t : Prop) : (term38 _119829 t) = t.
Proof. exact (@lem5718172 (_119829 -> Prop) t). Qed.
Lemma lem5718174 {_119829 : Type'} : (term36 _119829) = True.
Proof. exact (@lem5718173 _119829 True). Qed.
Lemma lem5718175 {_119826 _119829 : Type'} (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) : (term35 _119826 _119829 f x op) = True.
Proof. exact (TRANS (@lem5718170 _119826 _119829 f x op) (@lem5718174 _119829)). Qed.
Lemma lem5718176 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) : (term39 _119826 _119829 f op) = (term40 _119829).
Proof. exact (fun_ext (fun x : _119829 => @lem5718175 _119826 _119829 f x op)). Qed.
Lemma lem5718177 {_119829 : Type'} : (@all _119829) = (@all _119829).
Proof. exact (eq_refl (@all _119829)). Qed.
Lemma lem5718178 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) : (term41 _119826 _119829 f op) = (term42 _119829).
Proof. exact (MK_COMB (@lem5718177 _119829) (@lem5718176 _119826 _119829 f op)). Qed.
Lemma lem5718180 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5718181 {_119829 : Type'} (t : Prop) : (term37 _119829 t) = t.
Proof. exact (@lem5718180 _119829 t). Qed.
Lemma lem5718182 {_119829 : Type'} : (term42 _119829) = True.
Proof. exact (@lem5718181 _119829 True). Qed.
Lemma lem5718183 {_119826 _119829 : Type'} (f : _119829 -> _119826) (op : type1400 _119826) : (term41 _119826 _119829 f op) = True.
Proof. exact (TRANS (@lem5718178 _119826 _119829 f op) (@lem5718182 _119829)). Qed.
Lemma lem5718184 {_119826 _119829 : Type'} (op : type1400 _119826) : (term43 _119826 _119829 op) = (term44 _119826 _119829).
Proof. exact (fun_ext (fun f : _119829 -> _119826 => @lem5718183 _119826 _119829 f op)). Qed.
Lemma lem5718185 {_119826 _119829 : Type'} : (@all (_119829 -> _119826)) = (@all (_119829 -> _119826)).
Proof. exact (eq_refl (@all (_119829 -> _119826))). Qed.
Lemma lem5718186 {_119826 _119829 : Type'} (op : type1400 _119826) : (term45 _119826 _119829 op) = (term46 _119826 _119829).
Proof. exact (MK_COMB (@lem5718185 _119826 _119829) (@lem5718184 _119826 _119829 op)). Qed.
Lemma lem5718188 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5718189 {_119826 _119829 : Type'} (t : Prop) : (term47 _119826 _119829 t) = t.
Proof. exact (@lem5718188 (_119829 -> _119826) t). Qed.
Lemma lem5718190 {_119826 _119829 : Type'} : (term46 _119826 _119829) = True.
Proof. exact (@lem5718189 _119826 _119829 True). Qed.
Lemma lem5718191 {_119826 _119829 : Type'} (op : type1400 _119826) : (term45 _119826 _119829 op) = True.
Proof. exact (TRANS (@lem5718186 _119826 _119829 op) (@lem5718190 _119826 _119829)). Qed.
Lemma lem5718192 {_119826 _119829 : Type'} : (term48 _119826 _119829) = (term49 _119826).
Proof. exact (fun_ext (fun op : type1400 _119826 => @lem5718191 _119826 _119829 op)). Qed.
Lemma lem5718193 {_119826 : Type'} : (@all (_119826 -> _119826 -> _119826)) = (@all (_119826 -> _119826 -> _119826)).
Proof. exact (eq_refl (@all (_119826 -> _119826 -> _119826))). Qed.
Lemma lem5718194 {_119826 _119829 : Type'} : (term50 _119826 _119829) = (term51 _119826).
Proof. exact (MK_COMB (@lem5718193 _119826) (@lem5718192 _119826 _119829)). Qed.
Lemma lem5718196 {A : Type'} (t : Prop) : (term37 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5718197 {_119826 : Type'} (t : Prop) : (term52 _119826 t) = t.
Proof. exact (@lem5718196 (type1400 _119826) t). Qed.
Lemma lem5718198 {_119826 : Type'} : (term51 _119826) = True.
Proof. exact (@lem5718197 _119826 True). Qed.
Lemma lem5718199 {_119826 _119829 : Type'} : (term50 _119826 _119829) = True.
Proof. exact (TRANS (@lem5718194 _119826 _119829) (@lem5718198 _119826)). Qed.
Lemma lem5718200 {_119826 _119829 : Type'} : True = (term50 _119826 _119829).
Proof. exact (SYM (@lem5718199 _119826 _119829)). Qed.
Lemma lem5718201 {_119826 _119829 : Type'} : term50 _119826 _119829.
Proof. exact (EQ_MP (@lem5718200 _119826 _119829) (@lem0)). Qed.

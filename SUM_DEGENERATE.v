Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_DEGENERATE_term_abbrevs.
Require Import iterate_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Require Import thm7064171_spec.
Require Import thm7065437_spec.
Require Import thm82_spec.
Lemma lem7067133 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem7067134 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem7067135 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem7067134 A B s) (@lem7067133 A B s)). Qed.
Lemma lem7067136 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem7067135 A B s f). Qed.
Lemma lem7067137 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem7067138 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem7067137 A B s f) (@lem7067136 A B s f)). Qed.
Lemma lem7067139 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term4 A B s f op.
Proof. exact (@lem7067138 A B s f op). Qed.
Lemma lem7067140 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term4 A B s f op) = ((@support A B op f s) = (term5 A B s f op)).
Proof. exact (eq_refl (term4 A B s f op)). Qed.
Lemma lem7067142 {_119779 A : Type'} (f : A -> _119779) : term6 _119779 A f.
Proof. exact (@lem5718049 _119779 A f). Qed.
Lemma lem7067143 {_119779 A : Type'} (f : A -> _119779) : (term6 _119779 A f) = (term7 _119779 A f).
Proof. exact (eq_refl (term6 _119779 A f)). Qed.
Lemma lem7067144 {_119779 A : Type'} (f : A -> _119779) : term7 _119779 A f.
Proof. exact (EQ_MP (@lem7067143 _119779 A f) (@lem7067142 _119779 A f)). Qed.
Lemma lem7067145 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term8 _119779 A f s.
Proof. exact (@lem7067144 _119779 A f s). Qed.
Lemma lem7067146 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : (term8 _119779 A f s) = (term9 _119779 A f s).
Proof. exact (eq_refl (term8 _119779 A f s)). Qed.
Lemma lem7067147 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term9 _119779 A f s.
Proof. exact (EQ_MP (@lem7067146 _119779 A f s) (@lem7067145 _119779 A f s)). Qed.
Lemma lem7067148 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : term10 _119779 A f s op.
Proof. exact (@lem7067147 _119779 A f s op). Qed.
Lemma lem7067149 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (term10 _119779 A f s op) = ((@iterate _119779 A op s f) = (term11 _119779 A f s op)).
Proof. exact (eq_refl (term10 _119779 A f s op)). Qed.
Lemma lem7067164 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7067165 {_131446 : Type'} : (@sum _131446) = (@iterate real _131446 real_add).
Proof. exact (@lem7067164 _131446). Qed.
Lemma lem7067166 {_131446 : Type'} (s : _131446 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7067167 {_131446 : Type'} (s : _131446 -> Prop) : (@sum _131446 s) = (@iterate real _131446 real_add s).
Proof. exact (MK_COMB (@lem7067165 _131446) (@lem7067166 _131446 s)). Qed.
Lemma lem7067168 {_131446 : Type'} (f : _131446 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7067169 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (@sum _131446 s f) = (@iterate real _131446 real_add s f).
Proof. exact (MK_COMB (@lem7067167 _131446 s) (@lem7067168 _131446 f)). Qed.
Lemma lem7067170 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7067171 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term12 _131446 s f) = (term13 _131446 s f).
Proof. exact (MK_COMB (@lem7067170) (@lem7067169 _131446 s f)). Qed.
Lemma lem7067172 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem7067173 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : ((@sum _131446 s f) = term14) = ((@iterate real _131446 real_add s f) = term14).
Proof. exact (MK_COMB (@lem7067171 _131446 s f) (@lem7067172)). Qed.
Lemma lem7067176 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term15 _131446 s f) = (term15 _131446 s f).
Proof. exact (eq_refl (term15 _131446 s f)). Qed.
Lemma lem7067177 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term16 _131446 s f) = (term17 _131446 s f).
Proof. exact (MK_COMB (@lem7067176 _131446 s f) (@lem7067173 _131446 s f)). Qed.
Lemma lem7067180 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term17 _131446 s f) = (term16 _131446 s f).
Proof. exact (SYM (@lem7067177 _131446 s f)). Qed.
Lemma lem7067184 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term18 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7067185 (p : Prop) (q : Prop) (p' : Prop) : term19 p q p'.
Proof. exact (fun q' : Prop => @lem7067184 p q p' q'). Qed.
Lemma lem7067186 (p : Prop) (q : Prop) : term20 p q.
Proof. exact (fun p' : Prop => @lem7067185 p q p'). Qed.
Lemma lem7067187 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : term21 _131446 s f.
Proof. exact (@lem7067186 (term22 _131446 s f) ((@iterate real _131446 real_add s f) = term14)). Qed.
Lemma lem7067188 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (p' : Prop) : term23 _131446 s f p'.
Proof. exact (@lem7067187 _131446 s f p'). Qed.
Lemma lem7067189 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (p' : Prop) : (term23 _131446 s f p') = (term24 _131446 s f p').
Proof. exact (eq_refl (term23 _131446 s f p')). Qed.
Lemma lem7067190 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (p' : Prop) : term24 _131446 s f p'.
Proof. exact (EQ_MP (@lem7067189 _131446 s f p') (@lem7067188 _131446 s f p')). Qed.
Lemma lem7067191 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (p' : Prop) (q' : Prop) : term25 _131446 s f p' q'.
Proof. exact (@lem7067190 _131446 s f p' q'). Qed.
Lemma lem7067192 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (p' : Prop) (q' : Prop) : (term25 _131446 s f p' q') = (term26 _131446 s f p' q').
Proof. exact (eq_refl (term25 _131446 s f p' q')). Qed.
Lemma lem7067193 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (p' : Prop) (q' : Prop) : term26 _131446 s f p' q'.
Proof. exact (EQ_MP (@lem7067192 _131446 s f p' q') (@lem7067191 _131446 s f p' q')). Qed.
Lemma lem7067202 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term22 _131446 s f) = (term22 _131446 s f).
Proof. exact (eq_refl (term22 _131446 s f)). Qed.
Lemma lem7067203 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (q' : Prop) : term27 _131446 s f q'.
Proof. exact (@lem7067193 _131446 s f (term22 _131446 s f) q'). Qed.
Lemma lem7067204 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (q' : Prop) : term28 _131446 s f q'.
Proof. exact (@lem7067203 _131446 s f q' (@lem7067202 _131446 s f)). Qed.
Lemma lem7067205 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : term22 _131446 s f.
Proof. exact (h1). Qed.
Lemma lem7067206 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : term29 _131446 s f.
Proof. exact (@lem82 (term30 _131446 s f)). Qed.
Lemma lem7067211 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (@iterate _119779 A op s f) = (term11 _119779 A f s op).
Proof. exact (EQ_MP (@lem7067149 _119779 A f s op) (@lem7067148 _119779 A f s op)). Qed.
Lemma lem7067212 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) (op : type1627) : (@iterate real _131446 op s f) = (term31 _131446 f s op).
Proof. exact (@lem7067211 real _131446 f s op). Qed.
Lemma lem7067213 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) : (@iterate real _131446 real_add s f) = (term32 _131446 f s).
Proof. exact (@lem7067212 _131446 f s real_add). Qed.
Lemma lem7067215 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term33 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7067216 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term34 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7067215 _2963 g t e g' t' e'). Qed.
Lemma lem7067217 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term35 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7067216 _2963 g t e g' t'). Qed.
Lemma lem7067218 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term36 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7067217 _2963 g t e g'). Qed.
Lemma lem7067219 (g : Prop) (t : real) (e : real) : term37 g t e.
Proof. exact (@lem7067218 real g t e). Qed.
Lemma lem7067220 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) : term38 _131446 f s.
Proof. exact (@lem7067219 (term39 _131446 f s) (term40 _131446 f s) (@neutral real real_add)). Qed.
Lemma lem7067221 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) (g' : Prop) : term41 _131446 f s g'.
Proof. exact (@lem7067220 _131446 f s g'). Qed.
Lemma lem7067222 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) (g' : Prop) : (term41 _131446 f s g') = (term42 _131446 f s g').
Proof. exact (eq_refl (term41 _131446 f s g')). Qed.
Lemma lem7067223 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) (g' : Prop) : term42 _131446 f s g'.
Proof. exact (EQ_MP (@lem7067222 _131446 f s g') (@lem7067221 _131446 f s g')). Qed.
Lemma lem7067224 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) (g' : Prop) (t' : real) : term43 _131446 f s g' t'.
Proof. exact (@lem7067223 _131446 f s g' t'). Qed.
Lemma lem7067225 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) (g' : Prop) (t' : real) : (term43 _131446 f s g' t') = (term44 _131446 f s g' t').
Proof. exact (eq_refl (term43 _131446 f s g' t')). Qed.
Lemma lem7067226 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) (g' : Prop) (t' : real) : term44 _131446 f s g' t'.
Proof. exact (EQ_MP (@lem7067225 _131446 f s g' t') (@lem7067224 _131446 f s g' t')). Qed.
Lemma lem7067227 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) (g' : Prop) (t' : real) (e' : real) : term45 _131446 f s g' t' e'.
Proof. exact (@lem7067226 _131446 f s g' t' e'). Qed.
Lemma lem7067228 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) (g' : Prop) (t' : real) (e' : real) : (term45 _131446 f s g' t' e') = (term46 _131446 f s g' t' e').
Proof. exact (eq_refl (term45 _131446 f s g' t' e')). Qed.
Lemma lem7067229 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) (g' : Prop) (t' : real) (e' : real) : term46 _131446 f s g' t' e'.
Proof. exact (EQ_MP (@lem7067228 _131446 f s g' t' e') (@lem7067227 _131446 f s g' t' e')). Qed.
Lemma lem7067231 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term5 A B s f op).
Proof. exact (EQ_MP (@lem7067140 A B s f op) (@lem7067139 A B s f op)). Qed.
Lemma lem7067232 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (op : type1627) : (@support _131446 real op f s) = (term47 _131446 s f op).
Proof. exact (@lem7067231 _131446 real s f op). Qed.
Lemma lem7067233 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (@support _131446 real real_add f s) = (term48 _131446 s f).
Proof. exact (@lem7067232 _131446 s f real_add). Qed.
Lemma lem7067243 : (@neutral real real_add) = term14.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7067244 {_131446 : Type'} (f : _131446 -> real) (x : _131446) : (term49 _131446 f x) = (term49 _131446 f x).
Proof. exact (eq_refl (term49 _131446 f x)). Qed.
Lemma lem7067245 {_131446 : Type'} (f : _131446 -> real) (x : _131446) : ((f x) = (@neutral real real_add)) = ((f x) = term14).
Proof. exact (MK_COMB (@lem7067244 _131446 f x) (@lem7067243)). Qed.
Lemma lem7067248 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7067249 {_131446 : Type'} (f : _131446 -> real) (x : _131446) : (term50 _131446 f x) = (term51 _131446 f x).
Proof. exact (MK_COMB (@lem7067248) (@lem7067245 _131446 f x)). Qed.
Lemma lem7067252 {_131446 : Type'} (x : _131446) (s : _131446 -> Prop) : (term52 _131446 x s) = (term52 _131446 x s).
Proof. exact (eq_refl (term52 _131446 x s)). Qed.
Lemma lem7067253 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (x : _131446) : (term53 _131446 s f x) = (term54 _131446 s f x).
Proof. exact (MK_COMB (@lem7067252 _131446 x s) (@lem7067249 _131446 f x)). Qed.
Lemma lem7067258 {_131446 : Type'} (GEN_PVAR_237 : _131446) : (@SETSPEC _131446 GEN_PVAR_237) = (@SETSPEC _131446 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _131446 GEN_PVAR_237)). Qed.
Lemma lem7067259 {_131446 : Type'} (GEN_PVAR_237 : _131446) (s : _131446 -> Prop) (f : _131446 -> real) (x : _131446) : (term55 _131446 GEN_PVAR_237 s f x) = (term56 _131446 GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7067258 _131446 GEN_PVAR_237) (@lem7067253 _131446 s f x)). Qed.
Lemma lem7067264 {_131446 : Type'} (x : _131446) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7067265 {_131446 : Type'} (GEN_PVAR_237 : _131446) (s : _131446 -> Prop) (f : _131446 -> real) (x : _131446) : (term57 _131446 GEN_PVAR_237 s f x) = (term58 _131446 GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7067259 _131446 GEN_PVAR_237 s f x) (@lem7067264 _131446 x)). Qed.
Lemma lem7067270 {_131446 : Type'} (GEN_PVAR_237 : _131446) (s : _131446 -> Prop) (f : _131446 -> real) : (term59 _131446 GEN_PVAR_237 s f) = (term60 _131446 GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : _131446 => @lem7067265 _131446 GEN_PVAR_237 s f x)). Qed.
Lemma lem7067275 {_131446 : Type'} : (@ex _131446) = (@ex _131446).
Proof. exact (eq_refl (@ex _131446)). Qed.
Lemma lem7067276 {_131446 : Type'} (GEN_PVAR_237 : _131446) (s : _131446 -> Prop) (f : _131446 -> real) : (term61 _131446 GEN_PVAR_237 s f) = (term62 _131446 GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem7067275 _131446) (@lem7067270 _131446 GEN_PVAR_237 s f)). Qed.
Lemma lem7067285 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term63 _131446 s f) = (term64 _131446 s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _131446 => @lem7067276 _131446 GEN_PVAR_237 s f)). Qed.
Lemma lem7067294 {_131446 : Type'} : (@GSPEC _131446) = (@GSPEC _131446).
Proof. exact (eq_refl (@GSPEC _131446)). Qed.
Lemma lem7067295 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term48 _131446 s f) = (term65 _131446 s f).
Proof. exact (MK_COMB (@lem7067294 _131446) (@lem7067285 _131446 s f)). Qed.
Lemma lem7067304 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (@support _131446 real real_add f s) = (term65 _131446 s f).
Proof. exact (TRANS (@lem7067233 _131446 s f) (@lem7067295 _131446 s f)). Qed.
Lemma lem7067305 {_131446 : Type'} : (@FINITE _131446) = (@FINITE _131446).
Proof. exact (eq_refl (@FINITE _131446)). Qed.
Lemma lem7067306 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term39 _131446 f s) = (term30 _131446 s f).
Proof. exact (MK_COMB (@lem7067305 _131446) (@lem7067304 _131446 s f)). Qed.
Lemma lem7067308 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : (term30 _131446 s f) = False.
Proof. exact (@lem7067206 _131446 s f (@lem7067205 _131446 s f h1)). Qed.
Lemma lem7067309 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : (term30 _131446 s f) = False.
Proof. exact (@lem7067308 _131446 s f h1). Qed.
Lemma lem7067310 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : (term39 _131446 f s) = False.
Proof. exact (TRANS (@lem7067306 _131446 s f) (@lem7067309 _131446 s f h1)). Qed.
Lemma lem7067311 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) (t' : real) (e' : real) : term66 _131446 f s t' e'.
Proof. exact (@lem7067229 _131446 f s False t' e'). Qed.
Lemma lem7067312 {_131446 : Type'} (t' : real) (e' : real) (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : term67 _131446 f s t' e'.
Proof. exact (@lem7067311 _131446 f s t' e' (@lem7067310 _131446 s f h1)). Qed.
Lemma lem7067317 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term5 A B s f op).
Proof. exact (EQ_MP (@lem7067140 A B s f op) (@lem7067139 A B s f op)). Qed.
Lemma lem7067318 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (op : type1627) : (@support _131446 real op f s) = (term47 _131446 s f op).
Proof. exact (@lem7067317 _131446 real s f op). Qed.
Lemma lem7067319 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (@support _131446 real real_add f s) = (term48 _131446 s f).
Proof. exact (@lem7067318 _131446 s f real_add). Qed.
Lemma lem7067329 : (@neutral real real_add) = term14.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7067330 {_131446 : Type'} (f : _131446 -> real) (x : _131446) : (term49 _131446 f x) = (term49 _131446 f x).
Proof. exact (eq_refl (term49 _131446 f x)). Qed.
Lemma lem7067331 {_131446 : Type'} (f : _131446 -> real) (x : _131446) : ((f x) = (@neutral real real_add)) = ((f x) = term14).
Proof. exact (MK_COMB (@lem7067330 _131446 f x) (@lem7067329)). Qed.
Lemma lem7067334 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7067335 {_131446 : Type'} (f : _131446 -> real) (x : _131446) : (term50 _131446 f x) = (term51 _131446 f x).
Proof. exact (MK_COMB (@lem7067334) (@lem7067331 _131446 f x)). Qed.
Lemma lem7067338 {_131446 : Type'} (x : _131446) (s : _131446 -> Prop) : (term52 _131446 x s) = (term52 _131446 x s).
Proof. exact (eq_refl (term52 _131446 x s)). Qed.
Lemma lem7067339 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (x : _131446) : (term53 _131446 s f x) = (term54 _131446 s f x).
Proof. exact (MK_COMB (@lem7067338 _131446 x s) (@lem7067335 _131446 f x)). Qed.
Lemma lem7067344 {_131446 : Type'} (GEN_PVAR_237 : _131446) : (@SETSPEC _131446 GEN_PVAR_237) = (@SETSPEC _131446 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _131446 GEN_PVAR_237)). Qed.
Lemma lem7067345 {_131446 : Type'} (GEN_PVAR_237 : _131446) (s : _131446 -> Prop) (f : _131446 -> real) (x : _131446) : (term55 _131446 GEN_PVAR_237 s f x) = (term56 _131446 GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7067344 _131446 GEN_PVAR_237) (@lem7067339 _131446 s f x)). Qed.
Lemma lem7067350 {_131446 : Type'} (x : _131446) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7067351 {_131446 : Type'} (GEN_PVAR_237 : _131446) (s : _131446 -> Prop) (f : _131446 -> real) (x : _131446) : (term57 _131446 GEN_PVAR_237 s f x) = (term58 _131446 GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7067345 _131446 GEN_PVAR_237 s f x) (@lem7067350 _131446 x)). Qed.
Lemma lem7067356 {_131446 : Type'} (GEN_PVAR_237 : _131446) (s : _131446 -> Prop) (f : _131446 -> real) : (term59 _131446 GEN_PVAR_237 s f) = (term60 _131446 GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : _131446 => @lem7067351 _131446 GEN_PVAR_237 s f x)). Qed.
Lemma lem7067361 {_131446 : Type'} : (@ex _131446) = (@ex _131446).
Proof. exact (eq_refl (@ex _131446)). Qed.
Lemma lem7067362 {_131446 : Type'} (GEN_PVAR_237 : _131446) (s : _131446 -> Prop) (f : _131446 -> real) : (term61 _131446 GEN_PVAR_237 s f) = (term62 _131446 GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem7067361 _131446) (@lem7067356 _131446 GEN_PVAR_237 s f)). Qed.
Lemma lem7067371 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term63 _131446 s f) = (term64 _131446 s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _131446 => @lem7067362 _131446 GEN_PVAR_237 s f)). Qed.
Lemma lem7067380 {_131446 : Type'} : (@GSPEC _131446) = (@GSPEC _131446).
Proof. exact (eq_refl (@GSPEC _131446)). Qed.
Lemma lem7067381 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term48 _131446 s f) = (term65 _131446 s f).
Proof. exact (MK_COMB (@lem7067380 _131446) (@lem7067371 _131446 s f)). Qed.
Lemma lem7067390 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (@support _131446 real real_add f s) = (term65 _131446 s f).
Proof. exact (TRANS (@lem7067319 _131446 s f) (@lem7067381 _131446 s f)). Qed.
Lemma lem7067391 {_131446 : Type'} (f : _131446 -> real) : (term68 _131446 f) = (term68 _131446 f).
Proof. exact (eq_refl (term68 _131446 f)). Qed.
Lemma lem7067392 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term69 _131446 f s) = (term70 _131446 s f).
Proof. exact (MK_COMB (@lem7067391 _131446 f) (@lem7067390 _131446 s f)). Qed.
Lemma lem7067402 : (@neutral real real_add) = term14.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7067403 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term40 _131446 f s) = (term71 _131446 s f).
Proof. exact (MK_COMB (@lem7067392 _131446 s f) (@lem7067402)). Qed.
Lemma lem7067412 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : term72 _131446 s f.
Proof. exact (fun h0 : False => @lem7067403 _131446 s f). Qed.
Lemma lem7067413 {_131446 : Type'} (e' : real) (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : term73 _131446 s f e'.
Proof. exact (@lem7067312 _131446 (term71 _131446 s f) e' s f h1). Qed.
Lemma lem7067414 {_131446 : Type'} (e' : real) (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : term74 _131446 s f e'.
Proof. exact (@lem7067413 _131446 e' s f h1 (@lem7067412 _131446 s f)). Qed.
Lemma lem7067421 : (@neutral real real_add) = term14.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7067422 : term75.
Proof. exact (fun h0 : ~ False => @lem7067421). Qed.
Lemma lem7067423 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : term76 _131446 s f.
Proof. exact (@lem7067414 _131446 term14 s f h1). Qed.
Lemma lem7067424 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : (term32 _131446 f s) = (term77 _131446 s f).
Proof. exact (@lem7067423 _131446 s f h1 (@lem7067422)). Qed.
Lemma lem7067426 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7067427 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7067426 real t1 t2). Qed.
Lemma lem7067428 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term77 _131446 s f) = term14.
Proof. exact (@lem7067427 (term71 _131446 s f) term14). Qed.
Lemma lem7067429 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : (term32 _131446 f s) = term14.
Proof. exact (TRANS (@lem7067424 _131446 s f h1) (@lem7067428 _131446 s f)). Qed.
Lemma lem7067430 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : (@iterate real _131446 real_add s f) = term14.
Proof. exact (TRANS (@lem7067213 _131446 f s) (@lem7067429 _131446 s f h1)). Qed.
Lemma lem7067431 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7067432 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : (term13 _131446 s f) = term78.
Proof. exact (MK_COMB (@lem7067431) (@lem7067430 _131446 s f h1)). Qed.
Lemma lem7067433 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem7067434 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : ((@iterate real _131446 real_add s f) = term14) = (term14 = term14).
Proof. exact (MK_COMB (@lem7067432 _131446 s f h1) (@lem7067433)). Qed.
Lemma lem7067436 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7067437 (x : real) : (x = x) = True.
Proof. exact (@lem7067436 real x). Qed.
Lemma lem7067438 : (term14 = term14) = True.
Proof. exact (@lem7067437 term14). Qed.
Lemma lem7067439 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term22 _131446 s f) : ((@iterate real _131446 real_add s f) = term14) = True.
Proof. exact (TRANS (@lem7067434 _131446 s f h1) (@lem7067438)). Qed.
Lemma lem7067440 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : term79 _131446 s f.
Proof. exact (fun h0 : term22 _131446 s f => @lem7067439 _131446 s f h0). Qed.
Lemma lem7067441 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : term80 _131446 s f.
Proof. exact (@lem7067204 _131446 s f True). Qed.
Lemma lem7067442 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term17 _131446 s f) = (term81 _131446 s f).
Proof. exact (@lem7067441 _131446 s f (@lem7067440 _131446 s f)). Qed.
Lemma lem7067444 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7067445 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term81 _131446 s f) = True.
Proof. exact (@lem7067444 (term22 _131446 s f)). Qed.
Lemma lem7067446 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term17 _131446 s f) = True.
Proof. exact (TRANS (@lem7067442 _131446 s f) (@lem7067445 _131446 s f)). Qed.
Lemma lem7067447 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : True = (term17 _131446 s f).
Proof. exact (SYM (@lem7067446 _131446 s f)). Qed.
Lemma lem7067448 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : term17 _131446 s f.
Proof. exact (EQ_MP (@lem7067447 _131446 s f) (@lem0)). Qed.
Lemma lem7067449 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : term16 _131446 s f.
Proof. exact (EQ_MP (@lem7067180 _131446 s f) (@lem7067448 _131446 s f)). Qed.
Lemma lem7067454 {_131446 : Type'} (f : _131446 -> real) : term82 _131446 f.
Proof. exact (fun s : _131446 -> Prop => @lem7067449 _131446 s f). Qed.
Lemma lem7067459 {_131446 : Type'} : term83 _131446.
Proof. exact (fun f : _131446 -> real => @lem7067454 _131446 f). Qed.

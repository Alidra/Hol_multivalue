Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_SUM_RESTRICT_term_abbrevs.
Require Import SUM_RESTRICT_SET_spec.
Require Import SUM_SWAP_spec.
Require Import thm0_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Lemma lem7157062 {_133899 : Type'} (P : _133899 -> Prop) : term0 _133899 P.
Proof. exact (@lem7157061 _133899 P). Qed.
Lemma lem7157063 {_133899 : Type'} (P : _133899 -> Prop) : (term0 _133899 P) = (term1 _133899 P).
Proof. exact (eq_refl (term0 _133899 P)). Qed.
Lemma lem7157064 {_133899 : Type'} (P : _133899 -> Prop) : term1 _133899 P.
Proof. exact (EQ_MP (@lem7157063 _133899 P) (@lem7157062 _133899 P)). Qed.
Lemma lem7157065 {_133899 : Type'} (P : _133899 -> Prop) (s : _133899 -> Prop) : term2 _133899 P s.
Proof. exact (@lem7157064 _133899 P s). Qed.
Lemma lem7157066 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) : (term2 _133899 P s) = (term3 _133899 s P).
Proof. exact (eq_refl (term2 _133899 P s)). Qed.
Lemma lem7157067 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) : term3 _133899 s P.
Proof. exact (EQ_MP (@lem7157066 _133899 s P) (@lem7157065 _133899 P s)). Qed.
Lemma lem7157068 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : term4 _133899 s P f.
Proof. exact (@lem7157067 _133899 s P f). Qed.
Lemma lem7157069 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : (term4 _133899 s P f) = ((term5 _133899 s P f) = (term6 _133899 s P f)).
Proof. exact (eq_refl (term4 _133899 s P f)). Qed.
Lemma lem7157074 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term7 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7157075 (p : Prop) (q : Prop) (p' : Prop) : term8 p q p'.
Proof. exact (fun q' : Prop => @lem7157074 p q p' q'). Qed.
Lemma lem7157076 (p : Prop) (q : Prop) : term9 p q.
Proof. exact (fun p' : Prop => @lem7157075 p q p'). Qed.
Lemma lem7157077 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : term10 _133990 _133991 t s R f.
Proof. exact (@lem7157076 (term11 _133990 _133991 s t) ((term12 _133990 _133991 s t R f) = (term13 _133990 _133991 t s R f))). Qed.
Lemma lem7157078 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (p' : Prop) : term14 _133990 _133991 t s R f p'.
Proof. exact (@lem7157077 _133990 _133991 t s R f p'). Qed.
Lemma lem7157079 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (p' : Prop) : (term14 _133990 _133991 t s R f p') = (term15 _133990 _133991 t s R f p').
Proof. exact (eq_refl (term14 _133990 _133991 t s R f p')). Qed.
Lemma lem7157080 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (p' : Prop) : term15 _133990 _133991 t s R f p'.
Proof. exact (EQ_MP (@lem7157079 _133990 _133991 t s R f p') (@lem7157078 _133990 _133991 t s R f p')). Qed.
Lemma lem7157081 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (p' : Prop) (q' : Prop) : term16 _133990 _133991 t s R f p' q'.
Proof. exact (@lem7157080 _133990 _133991 t s R f p' q'). Qed.
Lemma lem7157082 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (p' : Prop) (q' : Prop) : (term16 _133990 _133991 t s R f p' q') = (term17 _133990 _133991 t s R f p' q').
Proof. exact (eq_refl (term16 _133990 _133991 t s R f p' q')). Qed.
Lemma lem7157083 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (p' : Prop) (q' : Prop) : term17 _133990 _133991 t s R f p' q'.
Proof. exact (EQ_MP (@lem7157082 _133990 _133991 t s R f p' q') (@lem7157081 _133990 _133991 t s R f p' q')). Qed.
Lemma lem7157086 {_133990 _133991 : Type'} (s : _133991 -> Prop) (t : _133990 -> Prop) : (term11 _133990 _133991 s t) = (term11 _133990 _133991 s t).
Proof. exact (eq_refl (term11 _133990 _133991 s t)). Qed.
Lemma lem7157087 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (q' : Prop) : term18 _133990 _133991 R f s t q'.
Proof. exact (@lem7157083 _133990 _133991 t s R f (term11 _133990 _133991 s t) q'). Qed.
Lemma lem7157088 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (q' : Prop) : term19 _133990 _133991 R f s t q'.
Proof. exact (@lem7157087 _133990 _133991 R f s t q' (@lem7157086 _133990 _133991 s t)). Qed.
Lemma lem7157099 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : (term5 _133899 s P f) = (term6 _133899 s P f).
Proof. exact (EQ_MP (@lem7157069 _133899 s P f) (@lem7157068 _133899 s P f)). Qed.
Lemma lem7157100 {_133990 : Type'} (s : _133990 -> Prop) (P : _133990 -> Prop) (f : _133990 -> real) : (term5 _133990 s P f) = (term6 _133990 s P f).
Proof. exact (@lem7157099 _133990 s P f). Qed.
Lemma lem7157101 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term20 _133990 _133991 t R f x) = (term21 _133990 _133991 t R f x).
Proof. exact (@lem7157100 _133990 t (term22 _133990 _133991 R x) (term23 _133990 _133991 f x)). Qed.
Lemma lem7157102 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (term24 _133990 _133991 R x y) = (R x y).
Proof. exact (eq_refl (term24 _133990 _133991 R x y)). Qed.
Lemma lem7157103 {_133990 : Type'} (y : _133990) (t : _133990 -> Prop) : (term25 _133990 y t) = (term25 _133990 y t).
Proof. exact (eq_refl (term25 _133990 y t)). Qed.
Lemma lem7157104 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (term26 _133990 _133991 t R x y) = (term27 _133990 _133991 t R x y).
Proof. exact (MK_COMB (@lem7157103 _133990 y t) (@lem7157102 _133990 _133991 R x y)). Qed.
Lemma lem7157105 {_133990 : Type'} (GEN_PVAR_317 : _133990) : (@SETSPEC _133990 GEN_PVAR_317) = (@SETSPEC _133990 GEN_PVAR_317).
Proof. exact (eq_refl (@SETSPEC _133990 GEN_PVAR_317)). Qed.
Lemma lem7157106 {_133990 _133991 : Type'} (GEN_PVAR_317 : _133990) (t : _133990 -> Prop) (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (term28 _133990 _133991 GEN_PVAR_317 t R x y) = (term29 _133990 _133991 GEN_PVAR_317 t R x y).
Proof. exact (MK_COMB (@lem7157105 _133990 GEN_PVAR_317) (@lem7157104 _133990 _133991 t R x y)). Qed.
Lemma lem7157107 {_133990 : Type'} (y : _133990) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7157108 {_133990 _133991 : Type'} (GEN_PVAR_317 : _133990) (t : _133990 -> Prop) (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (term30 _133990 _133991 GEN_PVAR_317 t R x y) = (term31 _133990 _133991 GEN_PVAR_317 t R x y).
Proof. exact (MK_COMB (@lem7157106 _133990 _133991 GEN_PVAR_317 t R x y) (@lem7157107 _133990 y)). Qed.
Lemma lem7157109 {_133990 _133991 : Type'} (GEN_PVAR_317 : _133990) (t : _133990 -> Prop) (R : type1470 _133990 _133991) (x : _133991) : (term32 _133990 _133991 GEN_PVAR_317 t R x) = (term33 _133990 _133991 GEN_PVAR_317 t R x).
Proof. exact (fun_ext (fun y : _133990 => @lem7157108 _133990 _133991 GEN_PVAR_317 t R x y)). Qed.
Lemma lem7157110 {_133990 : Type'} : (@ex _133990) = (@ex _133990).
Proof. exact (eq_refl (@ex _133990)). Qed.
Lemma lem7157111 {_133990 _133991 : Type'} (GEN_PVAR_317 : _133990) (t : _133990 -> Prop) (R : type1470 _133990 _133991) (x : _133991) : (term34 _133990 _133991 GEN_PVAR_317 t R x) = (term35 _133990 _133991 GEN_PVAR_317 t R x).
Proof. exact (MK_COMB (@lem7157110 _133990) (@lem7157109 _133990 _133991 GEN_PVAR_317 t R x)). Qed.
Lemma lem7157112 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (x : _133991) : (term36 _133990 _133991 t R x) = (term37 _133990 _133991 t R x).
Proof. exact (fun_ext (fun GEN_PVAR_317 : _133990 => @lem7157111 _133990 _133991 GEN_PVAR_317 t R x)). Qed.
Lemma lem7157113 {_133990 : Type'} : (@GSPEC _133990) = (@GSPEC _133990).
Proof. exact (eq_refl (@GSPEC _133990)). Qed.
Lemma lem7157114 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (x : _133991) : (term38 _133990 _133991 t R x) = (term39 _133990 _133991 t R x).
Proof. exact (MK_COMB (@lem7157113 _133990) (@lem7157112 _133990 _133991 t R x)). Qed.
Lemma lem7157115 {_133990 : Type'} : (@sum _133990) = (@sum _133990).
Proof. exact (eq_refl (@sum _133990)). Qed.
Lemma lem7157116 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (x : _133991) : (term40 _133990 _133991 t R x) = (term41 _133990 _133991 t R x).
Proof. exact (MK_COMB (@lem7157115 _133990) (@lem7157114 _133990 _133991 t R x)). Qed.
Lemma lem7157117 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) : (term23 _133990 _133991 f x) = (term23 _133990 _133991 f x).
Proof. exact (eq_refl (term23 _133990 _133991 f x)). Qed.
Lemma lem7157118 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term20 _133990 _133991 t R f x) = (term42 _133990 _133991 t R f x).
Proof. exact (MK_COMB (@lem7157116 _133990 _133991 t R x) (@lem7157117 _133990 _133991 f x)). Qed.
Lemma lem7157119 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7157120 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term43 _133990 _133991 t R f x) = (term44 _133990 _133991 t R f x).
Proof. exact (MK_COMB (@lem7157119) (@lem7157118 _133990 _133991 t R f x)). Qed.
Lemma lem7157121 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (term24 _133990 _133991 R x y) = (R x y).
Proof. exact (eq_refl (term24 _133990 _133991 R x y)). Qed.
Lemma lem7157122 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7157123 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (term45 _133990 _133991 R x y) = (term46 _133990 _133991 R x y).
Proof. exact (MK_COMB (@lem7157122) (@lem7157121 _133990 _133991 R x y)). Qed.
Lemma lem7157124 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term47 _133990 _133991 f x y) = (term47 _133990 _133991 f x y).
Proof. exact (eq_refl (term47 _133990 _133991 f x y)). Qed.
Lemma lem7157125 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term48 _133990 _133991 R f x y) = (term49 _133990 _133991 R f x y).
Proof. exact (MK_COMB (@lem7157123 _133990 _133991 R x y) (@lem7157124 _133990 _133991 f x y)). Qed.
Lemma lem7157126 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem7157127 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term51 _133990 _133991 R f x y) = (term52 _133990 _133991 R f x y).
Proof. exact (MK_COMB (@lem7157125 _133990 _133991 R f x y) (@lem7157126)). Qed.
Lemma lem7157128 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term53 _133990 _133991 R f x) = (term54 _133990 _133991 R f x).
Proof. exact (fun_ext (fun y : _133990 => @lem7157127 _133990 _133991 R f x y)). Qed.
Lemma lem7157129 {_133990 : Type'} (t : _133990 -> Prop) : (@sum _133990 t) = (@sum _133990 t).
Proof. exact (eq_refl (@sum _133990 t)). Qed.
Lemma lem7157130 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term21 _133990 _133991 t R f x) = (term55 _133990 _133991 t R f x).
Proof. exact (MK_COMB (@lem7157129 _133990 t) (@lem7157128 _133990 _133991 R f x)). Qed.
Lemma lem7157131 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : ((term20 _133990 _133991 t R f x) = (term21 _133990 _133991 t R f x)) = ((term42 _133990 _133991 t R f x) = (term55 _133990 _133991 t R f x)).
Proof. exact (MK_COMB (@lem7157120 _133990 _133991 t R f x) (@lem7157130 _133990 _133991 t R f x)). Qed.
Lemma lem7157132 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term42 _133990 _133991 t R f x) = (term55 _133990 _133991 t R f x).
Proof. exact (EQ_MP (@lem7157131 _133990 _133991 t R f x) (@lem7157101 _133990 _133991 t R f x)). Qed.
Lemma lem7157134 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term56 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7157135 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term57 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7157134 _2963 g t e g' t' e'). Qed.
Lemma lem7157136 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term58 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7157135 _2963 g t e g' t'). Qed.
Lemma lem7157137 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term59 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7157136 _2963 g t e g'). Qed.
Lemma lem7157138 (g : Prop) (t : real) (e : real) : term60 g t e.
Proof. exact (@lem7157137 real g t e). Qed.
Lemma lem7157139 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : term61 _133990 _133991 R f x y.
Proof. exact (@lem7157138 (R x y) (term47 _133990 _133991 f x y) term50). Qed.
Lemma lem7157140 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (g' : Prop) : term62 _133990 _133991 R f x y g'.
Proof. exact (@lem7157139 _133990 _133991 R f x y g'). Qed.
Lemma lem7157141 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (g' : Prop) : (term62 _133990 _133991 R f x y g') = (term63 _133990 _133991 R f x y g').
Proof. exact (eq_refl (term62 _133990 _133991 R f x y g')). Qed.
Lemma lem7157142 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (g' : Prop) : term63 _133990 _133991 R f x y g'.
Proof. exact (EQ_MP (@lem7157141 _133990 _133991 R f x y g') (@lem7157140 _133990 _133991 R f x y g')). Qed.
Lemma lem7157143 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (g' : Prop) (t' : real) : term64 _133990 _133991 R f x y g' t'.
Proof. exact (@lem7157142 _133990 _133991 R f x y g' t'). Qed.
Lemma lem7157144 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (g' : Prop) (t' : real) : (term64 _133990 _133991 R f x y g' t') = (term65 _133990 _133991 R f x y g' t').
Proof. exact (eq_refl (term64 _133990 _133991 R f x y g' t')). Qed.
Lemma lem7157145 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (g' : Prop) (t' : real) : term65 _133990 _133991 R f x y g' t'.
Proof. exact (EQ_MP (@lem7157144 _133990 _133991 R f x y g' t') (@lem7157143 _133990 _133991 R f x y g' t')). Qed.
Lemma lem7157146 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (g' : Prop) (t' : real) (e' : real) : term66 _133990 _133991 R f x y g' t' e'.
Proof. exact (@lem7157145 _133990 _133991 R f x y g' t' e'). Qed.
Lemma lem7157147 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (g' : Prop) (t' : real) (e' : real) : (term66 _133990 _133991 R f x y g' t' e') = (term67 _133990 _133991 R f x y g' t' e').
Proof. exact (eq_refl (term66 _133990 _133991 R f x y g' t' e')). Qed.
Lemma lem7157148 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (g' : Prop) (t' : real) (e' : real) : term67 _133990 _133991 R f x y g' t' e'.
Proof. exact (EQ_MP (@lem7157147 _133990 _133991 R f x y g' t' e') (@lem7157146 _133990 _133991 R f x y g' t' e')). Qed.
Lemma lem7157149 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem7157150 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (R : type1470 _133990 _133991) (x : _133991) (y : _133990) (t' : real) (e' : real) : term68 _133990 _133991 f R x y t' e'.
Proof. exact (@lem7157148 _133990 _133991 R f x y (R x y) t' e'). Qed.
Lemma lem7157151 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (R : type1470 _133990 _133991) (x : _133991) (y : _133990) (t' : real) (e' : real) : term69 _133990 _133991 f R x y t' e'.
Proof. exact (@lem7157150 _133990 _133991 f R x y t' e' (@lem7157149 _133990 _133991 R x y)). Qed.
Lemma lem7157156 {A B : Type'} (f : A -> B) (y : A) : (term70 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7157157 {_133990 : Type'} (f : _133990 -> real) (y : _133990) : (term71 _133990 f y) = (f y).
Proof. exact (@lem7157156 _133990 real f y). Qed.
Lemma lem7157158 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term72 _133990 _133991 f x y) = (term47 _133990 _133991 f x y).
Proof. exact (@lem7157157 _133990 (term23 _133990 _133991 f x) y). Qed.
Lemma lem7157159 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term47 _133990 _133991 f x y) = (f x y).
Proof. exact (eq_refl (term47 _133990 _133991 f x y)). Qed.
Lemma lem7157160 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) : (term73 _133990 _133991 f x) = (term23 _133990 _133991 f x).
Proof. exact (fun_ext (fun y : _133990 => @lem7157159 _133990 _133991 f x y)). Qed.
Lemma lem7157161 {_133990 : Type'} (y : _133990) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7157162 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term72 _133990 _133991 f x y) = (term47 _133990 _133991 f x y).
Proof. exact (MK_COMB (@lem7157160 _133990 _133991 f x) (@lem7157161 _133990 y)). Qed.
Lemma lem7157163 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7157164 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term74 _133990 _133991 f x y) = (term75 _133990 _133991 f x y).
Proof. exact (MK_COMB (@lem7157163) (@lem7157162 _133990 _133991 f x y)). Qed.
Lemma lem7157165 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term47 _133990 _133991 f x y) = (f x y).
Proof. exact (eq_refl (term47 _133990 _133991 f x y)). Qed.
Lemma lem7157166 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : ((term72 _133990 _133991 f x y) = (term47 _133990 _133991 f x y)) = ((term47 _133990 _133991 f x y) = (f x y)).
Proof. exact (MK_COMB (@lem7157164 _133990 _133991 f x y) (@lem7157165 _133990 _133991 f x y)). Qed.
Lemma lem7157167 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term47 _133990 _133991 f x y) = (f x y).
Proof. exact (EQ_MP (@lem7157166 _133990 _133991 f x y) (@lem7157158 _133990 _133991 f x y)). Qed.
Lemma lem7157168 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : term76 _133990 _133991 R f x y.
Proof. exact (fun h0 : R x y => @lem7157167 _133990 _133991 f x y). Qed.
Lemma lem7157169 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (e' : real) : term77 _133990 _133991 R f x y e'.
Proof. exact (@lem7157151 _133990 _133991 f R x y (f x y) e'). Qed.
Lemma lem7157170 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (e' : real) : term78 _133990 _133991 R f x y e'.
Proof. exact (@lem7157169 _133990 _133991 R f x y e' (@lem7157168 _133990 _133991 R f x y)). Qed.
Lemma lem7157174 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem7157175 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : term79 _133990 _133991 R x y.
Proof. exact (fun h0 : term80 _133990 _133991 R x y => @lem7157174). Qed.
Lemma lem7157176 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : term81 _133990 _133991 R f x y.
Proof. exact (@lem7157170 _133990 _133991 R f x y term50). Qed.
Lemma lem7157177 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term52 _133990 _133991 R f x y) = (term82 _133990 _133991 R f x y).
Proof. exact (@lem7157176 _133990 _133991 R f x y (@lem7157175 _133990 _133991 R x y)). Qed.
Lemma lem7157211 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term54 _133990 _133991 R f x) = (term83 _133990 _133991 R f x).
Proof. exact (fun_ext (fun y : _133990 => @lem7157177 _133990 _133991 R f x y)). Qed.
Lemma lem7157245 {_133990 : Type'} (t : _133990 -> Prop) : (@sum _133990 t) = (@sum _133990 t).
Proof. exact (eq_refl (@sum _133990 t)). Qed.
Lemma lem7157246 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term55 _133990 _133991 t R f x) = (term84 _133990 _133991 t R f x).
Proof. exact (MK_COMB (@lem7157245 _133990 t) (@lem7157211 _133990 _133991 R f x)). Qed.
Lemma lem7157280 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term42 _133990 _133991 t R f x) = (term84 _133990 _133991 t R f x).
Proof. exact (TRANS (@lem7157132 _133990 _133991 t R f x) (@lem7157246 _133990 _133991 t R f x)). Qed.
Lemma lem7157281 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term85 _133990 _133991 t R f) = (term86 _133990 _133991 t R f).
Proof. exact (fun_ext (fun x : _133991 => @lem7157280 _133990 _133991 t R f x)). Qed.
Lemma lem7157315 {_133991 : Type'} (s : _133991 -> Prop) : (@sum _133991 s) = (@sum _133991 s).
Proof. exact (eq_refl (@sum _133991 s)). Qed.
Lemma lem7157316 {_133990 _133991 : Type'} (s : _133991 -> Prop) (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term12 _133990 _133991 s t R f) = (term87 _133990 _133991 s t R f).
Proof. exact (MK_COMB (@lem7157315 _133991 s) (@lem7157281 _133990 _133991 t R f)). Qed.
Lemma lem7157350 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7157351 {_133990 _133991 : Type'} (s : _133991 -> Prop) (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term88 _133990 _133991 s t R f) = (term89 _133990 _133991 s t R f).
Proof. exact (MK_COMB (@lem7157350) (@lem7157316 _133990 _133991 s t R f)). Qed.
Lemma lem7157386 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : (term5 _133899 s P f) = (term6 _133899 s P f).
Proof. exact (EQ_MP (@lem7157069 _133899 s P f) (@lem7157068 _133899 s P f)). Qed.
Lemma lem7157387 {_133991 : Type'} (s : _133991 -> Prop) (P : _133991 -> Prop) (f : _133991 -> real) : (term5 _133991 s P f) = (term6 _133991 s P f).
Proof. exact (@lem7157386 _133991 s P f). Qed.
Lemma lem7157388 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) : (term90 _133990 _133991 s R f y) = (term91 _133990 _133991 s R f y).
Proof. exact (@lem7157387 _133991 s (term92 _133990 _133991 R y) (term93 _133990 _133991 f y)). Qed.
Lemma lem7157389 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (term94 _133990 _133991 R y x) = (R x y).
Proof. exact (eq_refl (term94 _133990 _133991 R y x)). Qed.
Lemma lem7157390 {_133991 : Type'} (x : _133991) (s : _133991 -> Prop) : (term25 _133991 x s) = (term25 _133991 x s).
Proof. exact (eq_refl (term25 _133991 x s)). Qed.
Lemma lem7157391 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (term95 _133990 _133991 s R y x) = (term96 _133990 _133991 s R x y).
Proof. exact (MK_COMB (@lem7157390 _133991 x s) (@lem7157389 _133990 _133991 R x y)). Qed.
Lemma lem7157392 {_133991 : Type'} (GEN_PVAR_318 : _133991) : (@SETSPEC _133991 GEN_PVAR_318) = (@SETSPEC _133991 GEN_PVAR_318).
Proof. exact (eq_refl (@SETSPEC _133991 GEN_PVAR_318)). Qed.
Lemma lem7157393 {_133990 _133991 : Type'} (GEN_PVAR_318 : _133991) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (term97 _133990 _133991 GEN_PVAR_318 s R y x) = (term98 _133990 _133991 GEN_PVAR_318 s R x y).
Proof. exact (MK_COMB (@lem7157392 _133991 GEN_PVAR_318) (@lem7157391 _133990 _133991 s R x y)). Qed.
Lemma lem7157394 {_133991 : Type'} (x : _133991) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7157395 {_133990 _133991 : Type'} (GEN_PVAR_318 : _133991) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (y : _133990) (x : _133991) : (term99 _133990 _133991 GEN_PVAR_318 s R y x) = (term100 _133990 _133991 GEN_PVAR_318 s R y x).
Proof. exact (MK_COMB (@lem7157393 _133990 _133991 GEN_PVAR_318 s R x y) (@lem7157394 _133991 x)). Qed.
Lemma lem7157396 {_133990 _133991 : Type'} (GEN_PVAR_318 : _133991) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (y : _133990) : (term101 _133990 _133991 GEN_PVAR_318 s R y) = (term102 _133990 _133991 GEN_PVAR_318 s R y).
Proof. exact (fun_ext (fun x : _133991 => @lem7157395 _133990 _133991 GEN_PVAR_318 s R y x)). Qed.
Lemma lem7157397 {_133991 : Type'} : (@ex _133991) = (@ex _133991).
Proof. exact (eq_refl (@ex _133991)). Qed.
Lemma lem7157398 {_133990 _133991 : Type'} (GEN_PVAR_318 : _133991) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (y : _133990) : (term103 _133990 _133991 GEN_PVAR_318 s R y) = (term104 _133990 _133991 GEN_PVAR_318 s R y).
Proof. exact (MK_COMB (@lem7157397 _133991) (@lem7157396 _133990 _133991 GEN_PVAR_318 s R y)). Qed.
Lemma lem7157399 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (y : _133990) : (term105 _133990 _133991 s R y) = (term106 _133990 _133991 s R y).
Proof. exact (fun_ext (fun GEN_PVAR_318 : _133991 => @lem7157398 _133990 _133991 GEN_PVAR_318 s R y)). Qed.
Lemma lem7157400 {_133991 : Type'} : (@GSPEC _133991) = (@GSPEC _133991).
Proof. exact (eq_refl (@GSPEC _133991)). Qed.
Lemma lem7157401 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (y : _133990) : (term107 _133990 _133991 s R y) = (term108 _133990 _133991 s R y).
Proof. exact (MK_COMB (@lem7157400 _133991) (@lem7157399 _133990 _133991 s R y)). Qed.
Lemma lem7157402 {_133991 : Type'} : (@sum _133991) = (@sum _133991).
Proof. exact (eq_refl (@sum _133991)). Qed.
Lemma lem7157403 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (y : _133990) : (term109 _133990 _133991 s R y) = (term110 _133990 _133991 s R y).
Proof. exact (MK_COMB (@lem7157402 _133991) (@lem7157401 _133990 _133991 s R y)). Qed.
Lemma lem7157404 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (y : _133990) : (term93 _133990 _133991 f y) = (term93 _133990 _133991 f y).
Proof. exact (eq_refl (term93 _133990 _133991 f y)). Qed.
Lemma lem7157405 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) : (term90 _133990 _133991 s R f y) = (term111 _133990 _133991 s R f y).
Proof. exact (MK_COMB (@lem7157403 _133990 _133991 s R y) (@lem7157404 _133990 _133991 f y)). Qed.
Lemma lem7157406 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7157407 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) : (term112 _133990 _133991 s R f y) = (term113 _133990 _133991 s R f y).
Proof. exact (MK_COMB (@lem7157406) (@lem7157405 _133990 _133991 s R f y)). Qed.
Lemma lem7157408 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (term94 _133990 _133991 R y x) = (R x y).
Proof. exact (eq_refl (term94 _133990 _133991 R y x)). Qed.
Lemma lem7157409 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7157410 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (term114 _133990 _133991 R y x) = (term46 _133990 _133991 R x y).
Proof. exact (MK_COMB (@lem7157409) (@lem7157408 _133990 _133991 R x y)). Qed.
Lemma lem7157411 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (y : _133990) (x : _133991) : (term115 _133990 _133991 f y x) = (term115 _133990 _133991 f y x).
Proof. exact (eq_refl (term115 _133990 _133991 f y x)). Qed.
Lemma lem7157412 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) (x : _133991) : (term116 _133990 _133991 R f y x) = (term117 _133990 _133991 R f y x).
Proof. exact (MK_COMB (@lem7157410 _133990 _133991 R x y) (@lem7157411 _133990 _133991 f y x)). Qed.
Lemma lem7157413 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem7157414 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) (x : _133991) : (term118 _133990 _133991 R f y x) = (term119 _133990 _133991 R f y x).
Proof. exact (MK_COMB (@lem7157412 _133990 _133991 R f y x) (@lem7157413)). Qed.
Lemma lem7157415 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) : (term120 _133990 _133991 R f y) = (term121 _133990 _133991 R f y).
Proof. exact (fun_ext (fun x : _133991 => @lem7157414 _133990 _133991 R f y x)). Qed.
Lemma lem7157416 {_133991 : Type'} (s : _133991 -> Prop) : (@sum _133991 s) = (@sum _133991 s).
Proof. exact (eq_refl (@sum _133991 s)). Qed.
Lemma lem7157417 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) : (term91 _133990 _133991 s R f y) = (term122 _133990 _133991 s R f y).
Proof. exact (MK_COMB (@lem7157416 _133991 s) (@lem7157415 _133990 _133991 R f y)). Qed.
Lemma lem7157418 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) : ((term90 _133990 _133991 s R f y) = (term91 _133990 _133991 s R f y)) = ((term111 _133990 _133991 s R f y) = (term122 _133990 _133991 s R f y)).
Proof. exact (MK_COMB (@lem7157407 _133990 _133991 s R f y) (@lem7157417 _133990 _133991 s R f y)). Qed.
Lemma lem7157419 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) : (term111 _133990 _133991 s R f y) = (term122 _133990 _133991 s R f y).
Proof. exact (EQ_MP (@lem7157418 _133990 _133991 s R f y) (@lem7157388 _133990 _133991 s R f y)). Qed.
Lemma lem7157421 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term56 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7157422 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term57 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7157421 _2963 g t e g' t' e'). Qed.
Lemma lem7157423 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term58 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7157422 _2963 g t e g' t'). Qed.
Lemma lem7157424 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term59 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7157423 _2963 g t e g'). Qed.
Lemma lem7157425 (g : Prop) (t : real) (e : real) : term60 g t e.
Proof. exact (@lem7157424 real g t e). Qed.
Lemma lem7157426 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) (x : _133991) : term123 _133990 _133991 R f y x.
Proof. exact (@lem7157425 (R x y) (term115 _133990 _133991 f y x) term50). Qed.
Lemma lem7157427 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) (x : _133991) (g' : Prop) : term124 _133990 _133991 R f y x g'.
Proof. exact (@lem7157426 _133990 _133991 R f y x g'). Qed.
Lemma lem7157428 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) (x : _133991) (g' : Prop) : (term124 _133990 _133991 R f y x g') = (term125 _133990 _133991 R f y x g').
Proof. exact (eq_refl (term124 _133990 _133991 R f y x g')). Qed.
Lemma lem7157429 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) (x : _133991) (g' : Prop) : term125 _133990 _133991 R f y x g'.
Proof. exact (EQ_MP (@lem7157428 _133990 _133991 R f y x g') (@lem7157427 _133990 _133991 R f y x g')). Qed.
Lemma lem7157430 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) (x : _133991) (g' : Prop) (t' : real) : term126 _133990 _133991 R f y x g' t'.
Proof. exact (@lem7157429 _133990 _133991 R f y x g' t'). Qed.
Lemma lem7157431 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) (x : _133991) (g' : Prop) (t' : real) : (term126 _133990 _133991 R f y x g' t') = (term127 _133990 _133991 R f y x g' t').
Proof. exact (eq_refl (term126 _133990 _133991 R f y x g' t')). Qed.
Lemma lem7157432 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) (x : _133991) (g' : Prop) (t' : real) : term127 _133990 _133991 R f y x g' t'.
Proof. exact (EQ_MP (@lem7157431 _133990 _133991 R f y x g' t') (@lem7157430 _133990 _133991 R f y x g' t')). Qed.
Lemma lem7157433 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) (x : _133991) (g' : Prop) (t' : real) (e' : real) : term128 _133990 _133991 R f y x g' t' e'.
Proof. exact (@lem7157432 _133990 _133991 R f y x g' t' e'). Qed.
Lemma lem7157434 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) (x : _133991) (g' : Prop) (t' : real) (e' : real) : (term128 _133990 _133991 R f y x g' t' e') = (term129 _133990 _133991 R f y x g' t' e').
Proof. exact (eq_refl (term128 _133990 _133991 R f y x g' t' e')). Qed.
Lemma lem7157435 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) (x : _133991) (g' : Prop) (t' : real) (e' : real) : term129 _133990 _133991 R f y x g' t' e'.
Proof. exact (EQ_MP (@lem7157434 _133990 _133991 R f y x g' t' e') (@lem7157433 _133990 _133991 R f y x g' t' e')). Qed.
Lemma lem7157436 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem7157437 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (R : type1470 _133990 _133991) (x : _133991) (y : _133990) (t' : real) (e' : real) : term130 _133990 _133991 f R x y t' e'.
Proof. exact (@lem7157435 _133990 _133991 R f y x (R x y) t' e'). Qed.
Lemma lem7157438 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (R : type1470 _133990 _133991) (x : _133991) (y : _133990) (t' : real) (e' : real) : term131 _133990 _133991 f R x y t' e'.
Proof. exact (@lem7157437 _133990 _133991 f R x y t' e' (@lem7157436 _133990 _133991 R x y)). Qed.
Lemma lem7157443 {A B : Type'} (f : A -> B) (y : A) : (term70 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7157444 {_133991 : Type'} (f : _133991 -> real) (y : _133991) : (term71 _133991 f y) = (f y).
Proof. exact (@lem7157443 _133991 real f y). Qed.
Lemma lem7157445 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (y : _133990) (x : _133991) : (term132 _133990 _133991 f y x) = (term115 _133990 _133991 f y x).
Proof. exact (@lem7157444 _133991 (term93 _133990 _133991 f y) x). Qed.
Lemma lem7157446 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term115 _133990 _133991 f y x) = (f x y).
Proof. exact (eq_refl (term115 _133990 _133991 f y x)). Qed.
Lemma lem7157447 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (y : _133990) : (term133 _133990 _133991 f y) = (term93 _133990 _133991 f y).
Proof. exact (fun_ext (fun x : _133991 => @lem7157446 _133990 _133991 f x y)). Qed.
Lemma lem7157448 {_133991 : Type'} (x : _133991) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7157449 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (y : _133990) (x : _133991) : (term132 _133990 _133991 f y x) = (term115 _133990 _133991 f y x).
Proof. exact (MK_COMB (@lem7157447 _133990 _133991 f y) (@lem7157448 _133991 x)). Qed.
Lemma lem7157450 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7157451 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (y : _133990) (x : _133991) : (term134 _133990 _133991 f y x) = (term135 _133990 _133991 f y x).
Proof. exact (MK_COMB (@lem7157450) (@lem7157449 _133990 _133991 f y x)). Qed.
Lemma lem7157452 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term115 _133990 _133991 f y x) = (f x y).
Proof. exact (eq_refl (term115 _133990 _133991 f y x)). Qed.
Lemma lem7157453 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : ((term132 _133990 _133991 f y x) = (term115 _133990 _133991 f y x)) = ((term115 _133990 _133991 f y x) = (f x y)).
Proof. exact (MK_COMB (@lem7157451 _133990 _133991 f y x) (@lem7157452 _133990 _133991 f x y)). Qed.
Lemma lem7157454 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term115 _133990 _133991 f y x) = (f x y).
Proof. exact (EQ_MP (@lem7157453 _133990 _133991 f x y) (@lem7157445 _133990 _133991 f y x)). Qed.
Lemma lem7157455 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : term136 _133990 _133991 R f x y.
Proof. exact (fun h0 : R x y => @lem7157454 _133990 _133991 f x y). Qed.
Lemma lem7157456 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (e' : real) : term137 _133990 _133991 R f x y e'.
Proof. exact (@lem7157438 _133990 _133991 f R x y (f x y) e'). Qed.
Lemma lem7157457 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) (e' : real) : term138 _133990 _133991 R f x y e'.
Proof. exact (@lem7157456 _133990 _133991 R f x y e' (@lem7157455 _133990 _133991 R f x y)). Qed.
Lemma lem7157461 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem7157462 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (x : _133991) (y : _133990) : term79 _133990 _133991 R x y.
Proof. exact (fun h0 : term80 _133990 _133991 R x y => @lem7157461). Qed.
Lemma lem7157463 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : term139 _133990 _133991 R f x y.
Proof. exact (@lem7157457 _133990 _133991 R f x y term50). Qed.
Lemma lem7157464 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term119 _133990 _133991 R f y x) = (term82 _133990 _133991 R f x y).
Proof. exact (@lem7157463 _133990 _133991 R f x y (@lem7157462 _133990 _133991 R x y)). Qed.
Lemma lem7157498 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) : (term121 _133990 _133991 R f y) = (term140 _133990 _133991 R f y).
Proof. exact (fun_ext (fun x : _133991 => @lem7157464 _133990 _133991 R f x y)). Qed.
Lemma lem7157532 {_133991 : Type'} (s : _133991 -> Prop) : (@sum _133991 s) = (@sum _133991 s).
Proof. exact (eq_refl (@sum _133991 s)). Qed.
Lemma lem7157533 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) : (term122 _133990 _133991 s R f y) = (term141 _133990 _133991 s R f y).
Proof. exact (MK_COMB (@lem7157532 _133991 s) (@lem7157498 _133990 _133991 R f y)). Qed.
Lemma lem7157567 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (y : _133990) : (term111 _133990 _133991 s R f y) = (term141 _133990 _133991 s R f y).
Proof. exact (TRANS (@lem7157419 _133990 _133991 s R f y) (@lem7157533 _133990 _133991 s R f y)). Qed.
Lemma lem7157568 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term142 _133990 _133991 s R f) = (term143 _133990 _133991 s R f).
Proof. exact (fun_ext (fun y : _133990 => @lem7157567 _133990 _133991 s R f y)). Qed.
Lemma lem7157602 {_133990 : Type'} (t : _133990 -> Prop) : (@sum _133990 t) = (@sum _133990 t).
Proof. exact (eq_refl (@sum _133990 t)). Qed.
Lemma lem7157603 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term13 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f).
Proof. exact (MK_COMB (@lem7157602 _133990 t) (@lem7157568 _133990 _133991 s R f)). Qed.
Lemma lem7157637 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : ((term12 _133990 _133991 s t R f) = (term13 _133990 _133991 t s R f)) = ((term87 _133990 _133991 s t R f) = (term144 _133990 _133991 t s R f)).
Proof. exact (MK_COMB (@lem7157351 _133990 _133991 s t R f) (@lem7157603 _133990 _133991 t s R f)). Qed.
Lemma lem7157706 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : term145 _133990 _133991 t s R f.
Proof. exact (fun h0 : term11 _133990 _133991 s t => @lem7157637 _133990 _133991 t s R f). Qed.
Lemma lem7157707 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : term146 _133990 _133991 t s R f.
Proof. exact (@lem7157088 _133990 _133991 R f s t ((term87 _133990 _133991 s t R f) = (term144 _133990 _133991 t s R f))). Qed.
Lemma lem7157708 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term147 _133990 _133991 t s R f) = (term148 _133990 _133991 t s R f).
Proof. exact (@lem7157707 _133990 _133991 t s R f (@lem7157706 _133990 _133991 t s R f)). Qed.
Lemma lem7157876 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term148 _133990 _133991 t s R f) = (term147 _133990 _133991 t s R f).
Proof. exact (SYM (@lem7157708 _133990 _133991 t s R f)). Qed.
Lemma lem7157877 {_133990 _133991 : Type'} (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : term11 _133990 _133991 s t.
Proof. exact (h1). Qed.
Lemma lem7157878 {A B : Type'} (h1 : term149 A B) : term149 A B.
Proof. exact (h1). Qed.
Lemma lem7157879 {A B : Type'} (f : type1416 A B) (h1 : term149 A B) : term150 A B f.
Proof. exact (@lem7157878 A B h1 f). Qed.
Lemma lem7157880 {A B : Type'} (f : type1416 A B) : (term150 A B f) = (term151 A B f).
Proof. exact (eq_refl (term150 A B f)). Qed.
Lemma lem7157881 {A B : Type'} (f : type1416 A B) (h1 : term149 A B) : term151 A B f.
Proof. exact (EQ_MP (@lem7157880 A B f) (@lem7157879 A B f h1)). Qed.
Lemma lem7157882 {A B : Type'} (f : type1416 A B) (s : A -> Prop) (h1 : term149 A B) : term152 A B f s.
Proof. exact (@lem7157881 A B f h1 s). Qed.
Lemma lem7157883 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term152 A B f s) = (term153 A B s f).
Proof. exact (eq_refl (term152 A B f s)). Qed.
Lemma lem7157884 {A B : Type'} (s : A -> Prop) (f : type1416 A B) (h1 : term149 A B) : term153 A B s f.
Proof. exact (EQ_MP (@lem7157883 A B s f) (@lem7157882 A B f s h1)). Qed.
Lemma lem7157885 {A B : Type'} (s : A -> Prop) (f : type1416 A B) (t : B -> Prop) (h1 : term149 A B) : term154 A B s f t.
Proof. exact (@lem7157884 A B s f h1 t). Qed.
Lemma lem7157886 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term154 A B s f t) = (term155 A B t s f).
Proof. exact (eq_refl (term154 A B s f t)). Qed.
Lemma lem7157887 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) (h1 : term149 A B) : term155 A B t s f.
Proof. exact (EQ_MP (@lem7157886 A B t s f) (@lem7157885 A B s f t h1)). Qed.
Lemma lem7157888 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term156 A B s t) : term156 A B s t.
Proof. exact (h1). Qed.
Lemma lem7157889 {A B : Type'} (f : type1416 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term149 A B) (h2 : term156 A B s t) : (term157 A B s t f) = (term158 A B t s f).
Proof. exact (@lem7157887 A B t s f h1 (@lem7157888 A B s t h2)). Qed.
Lemma lem7157890 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term149 A B) (h2 : term156 A B s t) : term159 A B t s.
Proof. exact (fun f : type1416 A B => @lem7157889 A B f s t h1 h2). Qed.
Lemma lem7157891 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term149 A B) : term160 A B t s.
Proof. exact (fun h0 : term156 A B s t => @lem7157890 A B s t h1 h0). Qed.
Lemma lem7157892 {A B : Type'} (s : A -> Prop) (h1 : term149 A B) : term161 A B s.
Proof. exact (fun t : B -> Prop => @lem7157891 A B t s h1). Qed.
Lemma lem7157893 {A B : Type'} (h1 : term149 A B) : term162 A B.
Proof. exact (fun s : A -> Prop => @lem7157892 A B s h1). Qed.
Lemma lem7157894 {A B : Type'} : term163 A B.
Proof. exact (fun h0 : term149 A B => @lem7157893 A B h0). Qed.
Lemma lem7157895 {A B : Type'} : term162 A B.
Proof. exact (@lem7157894 A B (@lem7124408 A B)). Qed.
Lemma lem7157896 {A B : Type'} (s : A -> Prop) : term164 A B s.
Proof. exact (@lem7157895 A B s). Qed.
Lemma lem7157897 {A B : Type'} (s : A -> Prop) : (term164 A B s) = (term161 A B s).
Proof. exact (eq_refl (term164 A B s)). Qed.
Lemma lem7157898 {A B : Type'} (s : A -> Prop) : term161 A B s.
Proof. exact (EQ_MP (@lem7157897 A B s) (@lem7157896 A B s)). Qed.
Lemma lem7157899 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term165 A B s t.
Proof. exact (@lem7157898 A B s t). Qed.
Lemma lem7157900 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term165 A B s t) = (term160 A B t s).
Proof. exact (eq_refl (term165 A B s t)). Qed.
Lemma lem7157903 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term160 A B t s.
Proof. exact (EQ_MP (@lem7157900 A B t s) (@lem7157899 A B s t)). Qed.
Lemma lem7157904 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) : term166 _133990 _133991 t s.
Proof. exact (@lem7157903 _133991 _133990 t s). Qed.
Lemma lem7157905 {_133990 _133991 : Type'} (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : term167 _133990 _133991 t s.
Proof. exact (@lem7157904 _133990 _133991 t s (@lem7157877 _133990 _133991 s t h1)). Qed.
Lemma lem7157906 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : term168 _133990 _133991 t s f.
Proof. exact (@lem7157905 _133990 _133991 s t h1 f). Qed.
Lemma lem7157907 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (f : type1472 _133990 _133991) : (term168 _133990 _133991 t s f) = ((term169 _133990 _133991 s t f) = (term170 _133990 _133991 t s f)).
Proof. exact (eq_refl (term168 _133990 _133991 t s f)). Qed.
Lemma lem7157912 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : (term169 _133990 _133991 s t f) = (term170 _133990 _133991 t s f).
Proof. exact (EQ_MP (@lem7157907 _133990 _133991 t s f) (@lem7157906 _133990 _133991 f s t h1)). Qed.
Lemma lem7157913 {_133990 _133991 : Type'} (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : (term169 _133990 _133991 s t f) = (term170 _133990 _133991 t s f).
Proof. exact (@lem7157912 _133990 _133991 f s t h1). Qed.
Lemma lem7157914 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : (term171 _133990 _133991 s t R f) = (term172 _133990 _133991 t s R f).
Proof. exact (@lem7157913 _133990 _133991 (term173 _133990 _133991 R f) s t h1). Qed.
Lemma lem7157915 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term174 _133990 _133991 R f x) = (term83 _133990 _133991 R f x).
Proof. exact (eq_refl (term174 _133990 _133991 R f x)). Qed.
Lemma lem7157916 {_133990 : Type'} (t : _133990 -> Prop) : (@sum _133990 t) = (@sum _133990 t).
Proof. exact (eq_refl (@sum _133990 t)). Qed.
Lemma lem7157917 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term175 _133990 _133991 t R f x) = (term84 _133990 _133991 t R f x).
Proof. exact (MK_COMB (@lem7157916 _133990 t) (@lem7157915 _133990 _133991 R f x)). Qed.
Lemma lem7157918 {_133990 _133991 : Type'} (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term176 _133990 _133991 t R f) = (term86 _133990 _133991 t R f).
Proof. exact (fun_ext (fun x : _133991 => @lem7157917 _133990 _133991 t R f x)). Qed.
Lemma lem7157919 {_133991 : Type'} (s : _133991 -> Prop) : (@sum _133991 s) = (@sum _133991 s).
Proof. exact (eq_refl (@sum _133991 s)). Qed.
Lemma lem7157920 {_133990 _133991 : Type'} (s : _133991 -> Prop) (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term171 _133990 _133991 s t R f) = (term87 _133990 _133991 s t R f).
Proof. exact (MK_COMB (@lem7157919 _133991 s) (@lem7157918 _133990 _133991 t R f)). Qed.
Lemma lem7157921 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7157922 {_133990 _133991 : Type'} (s : _133991 -> Prop) (t : _133990 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term177 _133990 _133991 s t R f) = (term89 _133990 _133991 s t R f).
Proof. exact (MK_COMB (@lem7157921) (@lem7157920 _133990 _133991 s t R f)). Qed.
Lemma lem7157923 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term174 _133990 _133991 R f x) = (term83 _133990 _133991 R f x).
Proof. exact (eq_refl (term174 _133990 _133991 R f x)). Qed.
Lemma lem7157924 {_133990 : Type'} (j : _133990) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem7157925 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (j : _133990) : (term178 _133990 _133991 R f x j) = (term179 _133990 _133991 R f x j).
Proof. exact (MK_COMB (@lem7157923 _133990 _133991 R f x) (@lem7157924 _133990 j)). Qed.
Lemma lem7157926 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (j : _133990) : (term180 _133990 _133991 R f j) = (term181 _133990 _133991 R f j).
Proof. exact (fun_ext (fun x : _133991 => @lem7157925 _133990 _133991 R f x j)). Qed.
Lemma lem7157927 {_133991 : Type'} (s : _133991 -> Prop) : (@sum _133991 s) = (@sum _133991 s).
Proof. exact (eq_refl (@sum _133991 s)). Qed.
Lemma lem7157928 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (j : _133990) : (term182 _133990 _133991 s R f j) = (term183 _133990 _133991 s R f j).
Proof. exact (MK_COMB (@lem7157927 _133991 s) (@lem7157926 _133990 _133991 R f j)). Qed.
Lemma lem7157929 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term184 _133990 _133991 s R f) = (term185 _133990 _133991 s R f).
Proof. exact (fun_ext (fun j : _133990 => @lem7157928 _133990 _133991 s R f j)). Qed.
Lemma lem7157930 {_133990 : Type'} (t : _133990 -> Prop) : (@sum _133990 t) = (@sum _133990 t).
Proof. exact (eq_refl (@sum _133990 t)). Qed.
Lemma lem7157931 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term172 _133990 _133991 t s R f) = (term186 _133990 _133991 t s R f).
Proof. exact (MK_COMB (@lem7157930 _133990 t) (@lem7157929 _133990 _133991 s R f)). Qed.
Lemma lem7157932 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : ((term171 _133990 _133991 s t R f) = (term172 _133990 _133991 t s R f)) = ((term87 _133990 _133991 s t R f) = (term186 _133990 _133991 t s R f)).
Proof. exact (MK_COMB (@lem7157922 _133990 _133991 s t R f) (@lem7157931 _133990 _133991 t s R f)). Qed.
Lemma lem7157933 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : (term87 _133990 _133991 s t R f) = (term186 _133990 _133991 t s R f).
Proof. exact (EQ_MP (@lem7157932 _133990 _133991 t s R f) (@lem7157914 _133990 _133991 R f s t h1)). Qed.
Lemma lem7157935 {A B : Type'} (f : A -> B) (y : A) : (term70 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7157936 {_133990 : Type'} (f : _133990 -> real) (y : _133990) : (term71 _133990 f y) = (f y).
Proof. exact (@lem7157935 _133990 real f y). Qed.
Lemma lem7157937 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (j : _133990) : (term187 _133990 _133991 R f x j) = (term179 _133990 _133991 R f x j).
Proof. exact (@lem7157936 _133990 (term83 _133990 _133991 R f x) j). Qed.
Lemma lem7157938 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (y : _133990) : (term179 _133990 _133991 R f x y) = (term82 _133990 _133991 R f x y).
Proof. exact (eq_refl (term179 _133990 _133991 R f x y)). Qed.
Lemma lem7157939 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) : (term188 _133990 _133991 R f x) = (term83 _133990 _133991 R f x).
Proof. exact (fun_ext (fun y : _133990 => @lem7157938 _133990 _133991 R f x y)). Qed.
Lemma lem7157940 {_133990 : Type'} (j : _133990) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem7157941 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (j : _133990) : (term187 _133990 _133991 R f x j) = (term179 _133990 _133991 R f x j).
Proof. exact (MK_COMB (@lem7157939 _133990 _133991 R f x) (@lem7157940 _133990 j)). Qed.
Lemma lem7157942 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7157943 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (j : _133990) : (term189 _133990 _133991 R f x j) = (term190 _133990 _133991 R f x j).
Proof. exact (MK_COMB (@lem7157942) (@lem7157941 _133990 _133991 R f x j)). Qed.
Lemma lem7157944 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (j : _133990) : (term179 _133990 _133991 R f x j) = (term82 _133990 _133991 R f x j).
Proof. exact (eq_refl (term179 _133990 _133991 R f x j)). Qed.
Lemma lem7157945 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (j : _133990) : ((term187 _133990 _133991 R f x j) = (term179 _133990 _133991 R f x j)) = ((term179 _133990 _133991 R f x j) = (term82 _133990 _133991 R f x j)).
Proof. exact (MK_COMB (@lem7157943 _133990 _133991 R f x j) (@lem7157944 _133990 _133991 R f x j)). Qed.
Lemma lem7157946 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (x : _133991) (j : _133990) : (term179 _133990 _133991 R f x j) = (term82 _133990 _133991 R f x j).
Proof. exact (EQ_MP (@lem7157945 _133990 _133991 R f x j) (@lem7157937 _133990 _133991 R f x j)). Qed.
Lemma lem7157947 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (j : _133990) : (term181 _133990 _133991 R f j) = (term140 _133990 _133991 R f j).
Proof. exact (fun_ext (fun x : _133991 => @lem7157946 _133990 _133991 R f x j)). Qed.
Lemma lem7157948 {_133991 : Type'} (s : _133991 -> Prop) : (@sum _133991 s) = (@sum _133991 s).
Proof. exact (eq_refl (@sum _133991 s)). Qed.
Lemma lem7157949 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (j : _133990) : (term183 _133990 _133991 s R f j) = (term141 _133990 _133991 s R f j).
Proof. exact (MK_COMB (@lem7157948 _133991 s) (@lem7157947 _133990 _133991 R f j)). Qed.
Lemma lem7157950 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term185 _133990 _133991 s R f) = (term143 _133990 _133991 s R f).
Proof. exact (fun_ext (fun j : _133990 => @lem7157949 _133990 _133991 s R f j)). Qed.
Lemma lem7157951 {_133990 : Type'} (t : _133990 -> Prop) : (@sum _133990 t) = (@sum _133990 t).
Proof. exact (eq_refl (@sum _133990 t)). Qed.
Lemma lem7157952 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term186 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f).
Proof. exact (MK_COMB (@lem7157951 _133990 t) (@lem7157950 _133990 _133991 s R f)). Qed.
Lemma lem7157953 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : (term87 _133990 _133991 s t R f) = (term144 _133990 _133991 t s R f).
Proof. exact (TRANS (@lem7157933 _133990 _133991 R f s t h1) (@lem7157952 _133990 _133991 t s R f)). Qed.
Lemma lem7157954 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7157955 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : (term89 _133990 _133991 s t R f) = (term191 _133990 _133991 t s R f).
Proof. exact (MK_COMB (@lem7157954) (@lem7157953 _133990 _133991 R f s t h1)). Qed.
Lemma lem7157956 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f).
Proof. exact (eq_refl (term144 _133990 _133991 t s R f)). Qed.
Lemma lem7157957 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : ((term87 _133990 _133991 s t R f) = (term144 _133990 _133991 t s R f)) = ((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)).
Proof. exact (MK_COMB (@lem7157955 _133990 _133991 R f s t h1) (@lem7157956 _133990 _133991 t s R f)). Qed.
Lemma lem7157959 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7157960 (x : real) : (x = x) = True.
Proof. exact (@lem7157959 real x). Qed.
Lemma lem7157961 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : ((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True.
Proof. exact (@lem7157960 (term144 _133990 _133991 t s R f)). Qed.
Lemma lem7157964 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term192 _133990 _133991 t s R f) = (term192 _133990 _133991 t s R f).
Proof. exact (eq_refl (term192 _133990 _133991 t s R f)). Qed.
Lemma lem7157965 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term192 _133990 _133991 t s R f) = (((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True).
Proof. exact (eq_refl (term192 _133990 _133991 t s R f)). Qed.
Lemma lem7157966 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term193 _133990 _133991 t s R f) = (term193 _133990 _133991 t s R f).
Proof. exact (eq_refl (term193 _133990 _133991 t s R f)). Qed.
Lemma lem7157967 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : ((term192 _133990 _133991 t s R f) = (term192 _133990 _133991 t s R f)) = ((term192 _133990 _133991 t s R f) = (((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True)).
Proof. exact (MK_COMB (@lem7157966 _133990 _133991 t s R f) (@lem7157965 _133990 _133991 t s R f)). Qed.
Lemma lem7157968 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term192 _133990 _133991 t s R f) = (((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True).
Proof. exact (eq_refl (term192 _133990 _133991 t s R f)). Qed.
Lemma lem7157969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7157970 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (term193 _133990 _133991 t s R f) = (term194 _133990 _133991 t s R f).
Proof. exact (MK_COMB (@lem7157969) (@lem7157968 _133990 _133991 t s R f)). Qed.
Lemma lem7157971 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True) = (((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True).
Proof. exact (eq_refl (((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True)). Qed.
Lemma lem7157972 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : ((term192 _133990 _133991 t s R f) = (((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True)) = ((((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True) = (((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True)).
Proof. exact (MK_COMB (@lem7157970 _133990 _133991 t s R f) (@lem7157971 _133990 _133991 t s R f)). Qed.
Lemma lem7157973 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : ((term192 _133990 _133991 t s R f) = (term192 _133990 _133991 t s R f)) = ((((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True) = (((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True)).
Proof. exact (TRANS (@lem7157967 _133990 _133991 t s R f) (@lem7157972 _133990 _133991 t s R f)). Qed.
Lemma lem7157974 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : (((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True) = (((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True).
Proof. exact (EQ_MP (@lem7157973 _133990 _133991 t s R f) (@lem7157964 _133990 _133991 t s R f)). Qed.
Lemma lem7157975 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : ((term144 _133990 _133991 t s R f) = (term144 _133990 _133991 t s R f)) = True.
Proof. exact (EQ_MP (@lem7157974 _133990 _133991 t s R f) (@lem7157961 _133990 _133991 t s R f)). Qed.
Lemma lem7157976 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : ((term87 _133990 _133991 s t R f) = (term144 _133990 _133991 t s R f)) = True.
Proof. exact (TRANS (@lem7157957 _133990 _133991 R f s t h1) (@lem7157975 _133990 _133991 t s R f)). Qed.
Lemma lem7157977 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : True = ((term87 _133990 _133991 s t R f) = (term144 _133990 _133991 t s R f)).
Proof. exact (SYM (@lem7157976 _133990 _133991 R f s t h1)). Qed.
Lemma lem7157978 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) (s : _133991 -> Prop) (t : _133990 -> Prop) (h1 : term11 _133990 _133991 s t) : (term87 _133990 _133991 s t R f) = (term144 _133990 _133991 t s R f).
Proof. exact (EQ_MP (@lem7157977 _133990 _133991 R f s t h1) (@lem0)). Qed.
Lemma lem7157979 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : term148 _133990 _133991 t s R f.
Proof. exact (fun h0 : term11 _133990 _133991 s t => @lem7157978 _133990 _133991 R f s t h0). Qed.
Lemma lem7157980 {_133990 _133991 : Type'} (t : _133990 -> Prop) (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : term147 _133990 _133991 t s R f.
Proof. exact (EQ_MP (@lem7157876 _133990 _133991 t s R f) (@lem7157979 _133990 _133991 t s R f)). Qed.
Lemma lem7157985 {_133990 _133991 : Type'} (s : _133991 -> Prop) (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : term195 _133990 _133991 s R f.
Proof. exact (fun t : _133990 -> Prop => @lem7157980 _133990 _133991 t s R f). Qed.
Lemma lem7157990 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) (f : type1472 _133990 _133991) : term196 _133990 _133991 R f.
Proof. exact (fun s : _133991 -> Prop => @lem7157985 _133990 _133991 s R f). Qed.
Lemma lem7157995 {_133990 _133991 : Type'} (R : type1470 _133990 _133991) : term197 _133990 _133991 R.
Proof. exact (fun f : type1472 _133990 _133991 => @lem7157990 _133990 _133991 R f). Qed.
Lemma lem7158000 {_133990 _133991 : Type'} : term198 _133990 _133991.
Proof. exact (fun R : type1470 _133990 _133991 => @lem7157995 _133990 _133991 R). Qed.

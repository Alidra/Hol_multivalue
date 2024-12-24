Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_SUPPORT_term_abbrevs.
Require Import SUPPORT_SUPPORT_spec.
Require Import iterate_spec.
Require Import thm0_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Lemma lem6930108 {_119851 _119862 : Type'} (op : type1400 _119851) : term0 _119851 _119862 op.
Proof. exact (@lem5718586 _119851 _119862 op). Qed.
Lemma lem6930109 {_119851 _119862 : Type'} (op : type1400 _119851) : (term0 _119851 _119862 op) = (term1 _119851 _119862 op).
Proof. exact (eq_refl (term0 _119851 _119862 op)). Qed.
Lemma lem6930110 {_119851 _119862 : Type'} (op : type1400 _119851) : term1 _119851 _119862 op.
Proof. exact (EQ_MP (@lem6930109 _119851 _119862 op) (@lem6930108 _119851 _119862 op)). Qed.
Lemma lem6930111 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) : term2 _119851 _119862 op f.
Proof. exact (@lem6930110 _119851 _119862 op f). Qed.
Lemma lem6930112 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) : (term2 _119851 _119862 op f) = (term3 _119851 _119862 op f).
Proof. exact (eq_refl (term2 _119851 _119862 op f)). Qed.
Lemma lem6930113 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) : term3 _119851 _119862 op f.
Proof. exact (EQ_MP (@lem6930112 _119851 _119862 op f) (@lem6930111 _119851 _119862 op f)). Qed.
Lemma lem6930114 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : term4 _119851 _119862 op f s.
Proof. exact (@lem6930113 _119851 _119862 op f s). Qed.
Lemma lem6930115 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : (term4 _119851 _119862 op f s) = ((term5 _119851 _119862 op f s) = (@support _119862 _119851 op f s)).
Proof. exact (eq_refl (term4 _119851 _119862 op f s)). Qed.
Lemma lem6930117 {_119779 A : Type'} (f : A -> _119779) : term6 _119779 A f.
Proof. exact (@lem5718049 _119779 A f). Qed.
Lemma lem6930118 {_119779 A : Type'} (f : A -> _119779) : (term6 _119779 A f) = (term7 _119779 A f).
Proof. exact (eq_refl (term6 _119779 A f)). Qed.
Lemma lem6930119 {_119779 A : Type'} (f : A -> _119779) : term7 _119779 A f.
Proof. exact (EQ_MP (@lem6930118 _119779 A f) (@lem6930117 _119779 A f)). Qed.
Lemma lem6930120 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term8 _119779 A f s.
Proof. exact (@lem6930119 _119779 A f s). Qed.
Lemma lem6930121 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : (term8 _119779 A f s) = (term9 _119779 A f s).
Proof. exact (eq_refl (term8 _119779 A f s)). Qed.
Lemma lem6930122 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term9 _119779 A f s.
Proof. exact (EQ_MP (@lem6930121 _119779 A f s) (@lem6930120 _119779 A f s)). Qed.
Lemma lem6930123 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : term10 _119779 A f s op.
Proof. exact (@lem6930122 _119779 A f s op). Qed.
Lemma lem6930124 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (term10 _119779 A f s op) = ((@iterate _119779 A op s f) = (term11 _119779 A f s op)).
Proof. exact (eq_refl (term10 _119779 A f s op)). Qed.
Lemma lem6930137 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930138 {_126695 : Type'} : (@nsum _126695) = (@iterate nat _126695 Nat.add).
Proof. exact (@lem6930137 _126695). Qed.
Lemma lem6930139 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (@support _126695 nat Nat.add f s) = (@support _126695 nat Nat.add f s).
Proof. exact (eq_refl (@support _126695 nat Nat.add f s)). Qed.
Lemma lem6930140 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (term12 _126695 f s) = (term13 _126695 f s).
Proof. exact (MK_COMB (@lem6930138 _126695) (@lem6930139 _126695 f s)). Qed.
Lemma lem6930141 {_126695 : Type'} (f : _126695 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6930142 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) : (term14 _126695 s f) = (term15 _126695 s f).
Proof. exact (MK_COMB (@lem6930140 _126695 f s) (@lem6930141 _126695 f)). Qed.
Lemma lem6930144 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (@iterate _119779 A op s f) = (term11 _119779 A f s op).
Proof. exact (EQ_MP (@lem6930124 _119779 A f s op) (@lem6930123 _119779 A f s op)). Qed.
Lemma lem6930145 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (op : type1606) : (@iterate nat _126695 op s f) = (term16 _126695 f s op).
Proof. exact (@lem6930144 nat _126695 f s op). Qed.
Lemma lem6930146 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (term15 _126695 s f) = (term17 _126695 f s).
Proof. exact (@lem6930145 _126695 f (@support _126695 nat Nat.add f s) Nat.add). Qed.
Lemma lem6930148 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term18 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6930149 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term19 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6930148 _2963 g t e g' t' e'). Qed.
Lemma lem6930150 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term20 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6930149 _2963 g t e g' t'). Qed.
Lemma lem6930151 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term21 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6930150 _2963 g t e g'). Qed.
Lemma lem6930152 (g : Prop) (t : nat) (e : nat) : term22 g t e.
Proof. exact (@lem6930151 nat g t e). Qed.
Lemma lem6930153 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : term23 _126695 f s.
Proof. exact (@lem6930152 (term24 _126695 f s) (term25 _126695 f s) (@neutral nat Nat.add)). Qed.
Lemma lem6930154 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (g' : Prop) : term26 _126695 f s g'.
Proof. exact (@lem6930153 _126695 f s g'). Qed.
Lemma lem6930155 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (g' : Prop) : (term26 _126695 f s g') = (term27 _126695 f s g').
Proof. exact (eq_refl (term26 _126695 f s g')). Qed.
Lemma lem6930156 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (g' : Prop) : term27 _126695 f s g'.
Proof. exact (EQ_MP (@lem6930155 _126695 f s g') (@lem6930154 _126695 f s g')). Qed.
Lemma lem6930157 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (g' : Prop) (t' : nat) : term28 _126695 f s g' t'.
Proof. exact (@lem6930156 _126695 f s g' t'). Qed.
Lemma lem6930158 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (g' : Prop) (t' : nat) : (term28 _126695 f s g' t') = (term29 _126695 f s g' t').
Proof. exact (eq_refl (term28 _126695 f s g' t')). Qed.
Lemma lem6930159 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (g' : Prop) (t' : nat) : term29 _126695 f s g' t'.
Proof. exact (EQ_MP (@lem6930158 _126695 f s g' t') (@lem6930157 _126695 f s g' t')). Qed.
Lemma lem6930160 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term30 _126695 f s g' t' e'.
Proof. exact (@lem6930159 _126695 f s g' t' e'). Qed.
Lemma lem6930161 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term30 _126695 f s g' t' e') = (term31 _126695 f s g' t' e').
Proof. exact (eq_refl (term30 _126695 f s g' t' e')). Qed.
Lemma lem6930162 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term31 _126695 f s g' t' e'.
Proof. exact (EQ_MP (@lem6930161 _126695 f s g' t' e') (@lem6930160 _126695 f s g' t' e')). Qed.
Lemma lem6930164 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : (term5 _119851 _119862 op f s) = (@support _119862 _119851 op f s).
Proof. exact (EQ_MP (@lem6930115 _119851 _119862 op f s) (@lem6930114 _119851 _119862 op f s)). Qed.
Lemma lem6930165 {_126695 : Type'} (op : type1606) (f : _126695 -> nat) (s : _126695 -> Prop) : (term32 _126695 op f s) = (@support _126695 nat op f s).
Proof. exact (@lem6930164 nat _126695 op f s). Qed.
Lemma lem6930166 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (term33 _126695 f s) = (@support _126695 nat Nat.add f s).
Proof. exact (@lem6930165 _126695 Nat.add f s). Qed.
Lemma lem6930167 {_126695 : Type'} : (@FINITE _126695) = (@FINITE _126695).
Proof. exact (eq_refl (@FINITE _126695)). Qed.
Lemma lem6930168 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (term24 _126695 f s) = (term34 _126695 f s).
Proof. exact (MK_COMB (@lem6930167 _126695) (@lem6930166 _126695 f s)). Qed.
Lemma lem6930169 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (t' : nat) (e' : nat) : term35 _126695 f s t' e'.
Proof. exact (@lem6930162 _126695 f s (term34 _126695 f s) t' e'). Qed.
Lemma lem6930170 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (t' : nat) (e' : nat) : term36 _126695 f s t' e'.
Proof. exact (@lem6930169 _126695 f s t' e' (@lem6930168 _126695 f s)). Qed.
Lemma lem6930175 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : (term5 _119851 _119862 op f s) = (@support _119862 _119851 op f s).
Proof. exact (EQ_MP (@lem6930115 _119851 _119862 op f s) (@lem6930114 _119851 _119862 op f s)). Qed.
Lemma lem6930176 {_126695 : Type'} (op : type1606) (f : _126695 -> nat) (s : _126695 -> Prop) : (term32 _126695 op f s) = (@support _126695 nat op f s).
Proof. exact (@lem6930175 nat _126695 op f s). Qed.
Lemma lem6930177 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (term33 _126695 f s) = (@support _126695 nat Nat.add f s).
Proof. exact (@lem6930176 _126695 Nat.add f s). Qed.
Lemma lem6930178 {_126695 : Type'} (f : _126695 -> nat) : (term37 _126695 f) = (term37 _126695 f).
Proof. exact (eq_refl (term37 _126695 f)). Qed.
Lemma lem6930179 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (term38 _126695 f s) = (term39 _126695 f s).
Proof. exact (MK_COMB (@lem6930178 _126695 f) (@lem6930177 _126695 f s)). Qed.
Lemma lem6930180 : (@neutral nat Nat.add) = (@neutral nat Nat.add).
Proof. exact (eq_refl (@neutral nat Nat.add)). Qed.
Lemma lem6930181 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (term25 _126695 f s) = (term40 _126695 f s).
Proof. exact (MK_COMB (@lem6930179 _126695 f s) (@lem6930180)). Qed.
Lemma lem6930182 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : term41 _126695 f s.
Proof. exact (fun h0 : term34 _126695 f s => @lem6930181 _126695 f s). Qed.
Lemma lem6930183 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (e' : nat) : term42 _126695 f s e'.
Proof. exact (@lem6930170 _126695 f s (term40 _126695 f s) e'). Qed.
Lemma lem6930184 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (e' : nat) : term43 _126695 f s e'.
Proof. exact (@lem6930183 _126695 f s e' (@lem6930182 _126695 f s)). Qed.
Lemma lem6930188 : (@neutral nat Nat.add) = (@neutral nat Nat.add).
Proof. exact (eq_refl (@neutral nat Nat.add)). Qed.
Lemma lem6930189 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : term44 _126695 f s.
Proof. exact (fun h0 : term45 _126695 f s => @lem6930188). Qed.
Lemma lem6930190 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : term46 _126695 f s.
Proof. exact (@lem6930184 _126695 f s (@neutral nat Nat.add)). Qed.
Lemma lem6930191 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (term17 _126695 f s) = (term47 _126695 f s).
Proof. exact (@lem6930190 _126695 f s (@lem6930189 _126695 f s)). Qed.
Lemma lem6930225 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (term15 _126695 s f) = (term47 _126695 f s).
Proof. exact (TRANS (@lem6930146 _126695 f s) (@lem6930191 _126695 f s)). Qed.
Lemma lem6930226 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (term14 _126695 s f) = (term47 _126695 f s).
Proof. exact (TRANS (@lem6930142 _126695 s f) (@lem6930225 _126695 f s)). Qed.
Lemma lem6930227 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6930228 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (term48 _126695 s f) = (term49 _126695 f s).
Proof. exact (MK_COMB (@lem6930227) (@lem6930226 _126695 f s)). Qed.
Lemma lem6930263 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930264 {_126695 : Type'} : (@nsum _126695) = (@iterate nat _126695 Nat.add).
Proof. exact (@lem6930263 _126695). Qed.
Lemma lem6930265 {_126695 : Type'} (s : _126695 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6930266 {_126695 : Type'} (s : _126695 -> Prop) : (@nsum _126695 s) = (@iterate nat _126695 Nat.add s).
Proof. exact (MK_COMB (@lem6930264 _126695) (@lem6930265 _126695 s)). Qed.
Lemma lem6930267 {_126695 : Type'} (f : _126695 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6930268 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) : (@nsum _126695 s f) = (@iterate nat _126695 Nat.add s f).
Proof. exact (MK_COMB (@lem6930266 _126695 s) (@lem6930267 _126695 f)). Qed.
Lemma lem6930270 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (@iterate _119779 A op s f) = (term11 _119779 A f s op).
Proof. exact (EQ_MP (@lem6930124 _119779 A f s op) (@lem6930123 _119779 A f s op)). Qed.
Lemma lem6930271 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) (op : type1606) : (@iterate nat _126695 op s f) = (term16 _126695 f s op).
Proof. exact (@lem6930270 nat _126695 f s op). Qed.
Lemma lem6930272 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (@iterate nat _126695 Nat.add s f) = (term47 _126695 f s).
Proof. exact (@lem6930271 _126695 f s Nat.add). Qed.
Lemma lem6930306 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : (@nsum _126695 s f) = (term47 _126695 f s).
Proof. exact (TRANS (@lem6930268 _126695 s f) (@lem6930272 _126695 f s)). Qed.
Lemma lem6930307 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : ((term14 _126695 s f) = (@nsum _126695 s f)) = ((term47 _126695 f s) = (term47 _126695 f s)).
Proof. exact (MK_COMB (@lem6930228 _126695 f s) (@lem6930306 _126695 f s)). Qed.
Lemma lem6930309 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6930310 (x : nat) : (x = x) = True.
Proof. exact (@lem6930309 nat x). Qed.
Lemma lem6930311 {_126695 : Type'} (f : _126695 -> nat) (s : _126695 -> Prop) : ((term47 _126695 f s) = (term47 _126695 f s)) = True.
Proof. exact (@lem6930310 (term47 _126695 f s)). Qed.
Lemma lem6930312 {_126695 : Type'} (s : _126695 -> Prop) (f : _126695 -> nat) : ((term14 _126695 s f) = (@nsum _126695 s f)) = True.
Proof. exact (TRANS (@lem6930307 _126695 f s) (@lem6930311 _126695 f s)). Qed.
Lemma lem6930313 {_126695 : Type'} (f : _126695 -> nat) : (term50 _126695 f) = (term51 _126695).
Proof. exact (fun_ext (fun s : _126695 -> Prop => @lem6930312 _126695 s f)). Qed.
Lemma lem6930314 {_126695 : Type'} : (@all (_126695 -> Prop)) = (@all (_126695 -> Prop)).
Proof. exact (eq_refl (@all (_126695 -> Prop))). Qed.
Lemma lem6930315 {_126695 : Type'} (f : _126695 -> nat) : (term52 _126695 f) = (term53 _126695).
Proof. exact (MK_COMB (@lem6930314 _126695) (@lem6930313 _126695 f)). Qed.
Lemma lem6930317 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6930318 {_126695 : Type'} (t : Prop) : (term55 _126695 t) = t.
Proof. exact (@lem6930317 (_126695 -> Prop) t). Qed.
Lemma lem6930319 {_126695 : Type'} : (term53 _126695) = True.
Proof. exact (@lem6930318 _126695 True). Qed.
Lemma lem6930320 {_126695 : Type'} (f : _126695 -> nat) : (term52 _126695 f) = True.
Proof. exact (TRANS (@lem6930315 _126695 f) (@lem6930319 _126695)). Qed.
Lemma lem6930321 {_126695 : Type'} : (term56 _126695) = (term57 _126695).
Proof. exact (fun_ext (fun f : _126695 -> nat => @lem6930320 _126695 f)). Qed.
Lemma lem6930322 {_126695 : Type'} : (@all (_126695 -> nat)) = (@all (_126695 -> nat)).
Proof. exact (eq_refl (@all (_126695 -> nat))). Qed.
Lemma lem6930323 {_126695 : Type'} : (term58 _126695) = (term59 _126695).
Proof. exact (MK_COMB (@lem6930322 _126695) (@lem6930321 _126695)). Qed.
Lemma lem6930325 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6930326 {_126695 : Type'} (t : Prop) : (term60 _126695 t) = t.
Proof. exact (@lem6930325 (_126695 -> nat) t). Qed.
Lemma lem6930327 {_126695 : Type'} : (term59 _126695) = True.
Proof. exact (@lem6930326 _126695 True). Qed.
Lemma lem6930328 {_126695 : Type'} : (term58 _126695) = True.
Proof. exact (TRANS (@lem6930323 _126695) (@lem6930327 _126695)). Qed.
Lemma lem6930329 {_126695 : Type'} : True = (term58 _126695).
Proof. exact (SYM (@lem6930328 _126695)). Qed.
Lemma lem6930330 {_126695 : Type'} : term58 _126695.
Proof. exact (EQ_MP (@lem6930329 _126695) (@lem0)). Qed.

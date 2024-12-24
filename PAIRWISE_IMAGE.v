Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_IMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import IN_IMAGE_spec.
Require Import pairwise_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Lemma lem4810018 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4810019 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4810020 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4810019 t1) (@lem4810018 t1)). Qed.
Lemma lem4810021 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4810020 t1 t2). Qed.
Lemma lem4810022 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4810023 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4810022 t1 t2) (@lem4810021 t1 t2)). Qed.
Lemma lem4810024 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4810023 t1 t2 t3). Qed.
Lemma lem4810025 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4810026 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4810025 t1 t2 t3) (@lem4810024 t1 t2 t3)). Qed.
Lemma lem4810027 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4810026 t1 t2 t3)). Qed.
Lemma lem4810028 {A B : Type'} (y : B) : term7 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4810029 {A B : Type'} (y : B) : (term7 A B y) = (term8 A B y).
Proof. exact (eq_refl (term7 A B y)). Qed.
Lemma lem4810030 {A B : Type'} (y : B) : term8 A B y.
Proof. exact (EQ_MP (@lem4810029 A B y) (@lem4810028 A B y)). Qed.
Lemma lem4810031 {A B : Type'} (y : B) (s : A -> Prop) : term9 A B y s.
Proof. exact (@lem4810030 A B y s). Qed.
Lemma lem4810032 {A B : Type'} (y : B) (s : A -> Prop) : (term9 A B y s) = (term10 A B y s).
Proof. exact (eq_refl (term9 A B y s)). Qed.
Lemma lem4810033 {A B : Type'} (y : B) (s : A -> Prop) : term10 A B y s.
Proof. exact (EQ_MP (@lem4810032 A B y s) (@lem4810031 A B y s)). Qed.
Lemma lem4810034 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term11 A B y s f.
Proof. exact (@lem4810033 A B y s f). Qed.
Lemma lem4810035 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y s f) = ((term12 A B y f s) = (term13 A B y f s)).
Proof. exact (eq_refl (term11 A B y s f)). Qed.
Lemma lem4810037 {_110510 : Type'} (s : _110510 -> Prop) : term14 _110510 s.
Proof. exact (@lem4794393 _110510 s). Qed.
Lemma lem4810038 {_110510 : Type'} (s : _110510 -> Prop) : (term14 _110510 s) = (term15 _110510 s).
Proof. exact (eq_refl (term14 _110510 s)). Qed.
Lemma lem4810039 {_110510 : Type'} (s : _110510 -> Prop) : term15 _110510 s.
Proof. exact (EQ_MP (@lem4810038 _110510 s) (@lem4810037 _110510 s)). Qed.
Lemma lem4810040 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : term16 _110510 s r.
Proof. exact (@lem4810039 _110510 s r). Qed.
Lemma lem4810041 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (term16 _110510 s r) = ((@pairwise _110510 r s) = (term17 _110510 s r)).
Proof. exact (eq_refl (term16 _110510 s r)). Qed.
Lemma lem4810054 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term17 _110510 s r).
Proof. exact (EQ_MP (@lem4810041 _110510 s r) (@lem4810040 _110510 s r)). Qed.
Lemma lem4810055 {_110796 : Type'} (s : _110796 -> Prop) (r : type1402 _110796) : (@pairwise _110796 r s) = (term17 _110796 s r).
Proof. exact (@lem4810054 _110796 s r). Qed.
Lemma lem4810056 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term18 _110796 _110799 r f s) = (term19 _110796 _110799 f s r).
Proof. exact (@lem4810055 _110796 (@IMAGE _110799 _110796 f s) r). Qed.
Lemma lem4810070 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem4810035 A B y f s) (@lem4810034 A B y s f)). Qed.
Lemma lem4810071 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term20 _110796 _110799 y f s) = (term21 _110796 _110799 y f s).
Proof. exact (@lem4810070 _110799 _110796 y f s). Qed.
Lemma lem4810072 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term20 _110796 _110799 x f s) = (term21 _110796 _110799 x f s).
Proof. exact (@lem4810071 _110796 _110799 x f s). Qed.
Lemma lem4810081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4810082 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term22 _110796 _110799 x f s) = (term23 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4810081) (@lem4810072 _110796 _110799 x f s)). Qed.
Lemma lem4810086 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem4810035 A B y f s) (@lem4810034 A B y s f)). Qed.
Lemma lem4810087 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term20 _110796 _110799 y f s) = (term21 _110796 _110799 y f s).
Proof. exact (@lem4810086 _110799 _110796 y f s). Qed.
Lemma lem4810096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4810097 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term22 _110796 _110799 y f s) = (term23 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4810096) (@lem4810087 _110796 _110799 y f s)). Qed.
Lemma lem4810100 {_110796 : Type'} (x : _110796) (y : _110796) : (term24 _110796 x y) = (term24 _110796 x y).
Proof. exact (eq_refl (term24 _110796 x y)). Qed.
Lemma lem4810101 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term25 _110796 _110799 f s x y) = (term26 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4810097 _110796 _110799 y f s) (@lem4810100 _110796 x y)). Qed.
Lemma lem4810104 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term27 _110796 _110799 f s x y) = (term28 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4810082 _110796 _110799 x f s) (@lem4810101 _110796 _110799 f s x y)). Qed.
Lemma lem4810107 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4810108 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term29 _110796 _110799 f s x y) = (term30 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4810107) (@lem4810104 _110796 _110799 f s x y)). Qed.
Lemma lem4810109 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4810110 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term31 _110796 _110799 f s r x y) = (term32 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4810108 _110796 _110799 f s x y) (@lem4810109 _110796 r x y)). Qed.
Lemma lem4810113 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term33 _110796 _110799 f s r x) = (term34 _110796 _110799 f s r x).
Proof. exact (fun_ext (fun y : _110796 => @lem4810110 _110796 _110799 f s r x y)). Qed.
Lemma lem4810114 {_110796 : Type'} : (@all _110796) = (@all _110796).
Proof. exact (eq_refl (@all _110796)). Qed.
Lemma lem4810115 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term35 _110796 _110799 f s r x) = (term36 _110796 _110799 f s r x).
Proof. exact (MK_COMB (@lem4810114 _110796) (@lem4810113 _110796 _110799 f s r x)). Qed.
Lemma lem4810120 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term37 _110796 _110799 f s r) = (term38 _110796 _110799 f s r).
Proof. exact (fun_ext (fun x : _110796 => @lem4810115 _110796 _110799 f s r x)). Qed.
Lemma lem4810121 {_110796 : Type'} : (@all _110796) = (@all _110796).
Proof. exact (eq_refl (@all _110796)). Qed.
Lemma lem4810122 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term19 _110796 _110799 f s r) = (term39 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4810121 _110796) (@lem4810120 _110796 _110799 f s r)). Qed.
Lemma lem4810127 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term18 _110796 _110799 r f s) = (term39 _110796 _110799 f s r).
Proof. exact (TRANS (@lem4810056 _110796 _110799 f s r) (@lem4810122 _110796 _110799 f s r)). Qed.
Lemma lem4810128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4810129 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term40 _110796 _110799 r f s) = (term41 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4810128) (@lem4810127 _110796 _110799 f s r)). Qed.
Lemma lem4810131 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term17 _110510 s r).
Proof. exact (EQ_MP (@lem4810041 _110510 s r) (@lem4810040 _110510 s r)). Qed.
Lemma lem4810132 {_110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110799) : (@pairwise _110799 r s) = (term17 _110799 s r).
Proof. exact (@lem4810131 _110799 s r). Qed.
Lemma lem4810133 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term42 _110796 _110799 r f s) = (term43 _110796 _110799 s r f).
Proof. exact (@lem4810132 _110799 s (term44 _110796 _110799 r f)). Qed.
Lemma lem4810151 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4810152 {_110799 : Type'} (f : type1402 _110799) (y : _110799) : (term46 _110799 f y) = (f y).
Proof. exact (@lem4810151 _110799 (_110799 -> Prop) f y). Qed.
Lemma lem4810153 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (x : _110799) : (term47 _110796 _110799 r f x) = (term48 _110796 _110799 r f x).
Proof. exact (@lem4810152 _110799 (term44 _110796 _110799 r f) x). Qed.
Lemma lem4810154 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term48 _110796 _110799 r f x) = (term49 _110796 _110799 r x f).
Proof. exact (eq_refl (term48 _110796 _110799 r f x)). Qed.
Lemma lem4810155 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) : (term50 _110796 _110799 r f) = (term44 _110796 _110799 r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4810154 _110796 _110799 r x f)). Qed.
Lemma lem4810156 {_110799 : Type'} (x : _110799) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4810157 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (x : _110799) : (term47 _110796 _110799 r f x) = (term48 _110796 _110799 r f x).
Proof. exact (MK_COMB (@lem4810155 _110796 _110799 r f) (@lem4810156 _110799 x)). Qed.
Lemma lem4810158 {_110799 : Type'} : (@eq (_110799 -> Prop)) = (@eq (_110799 -> Prop)).
Proof. exact (eq_refl (@eq (_110799 -> Prop))). Qed.
Lemma lem4810159 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (x : _110799) : (term51 _110796 _110799 r f x) = (term52 _110796 _110799 r f x).
Proof. exact (MK_COMB (@lem4810158 _110799) (@lem4810157 _110796 _110799 r f x)). Qed.
Lemma lem4810160 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term48 _110796 _110799 r f x) = (term49 _110796 _110799 r x f).
Proof. exact (eq_refl (term48 _110796 _110799 r f x)). Qed.
Lemma lem4810161 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : ((term47 _110796 _110799 r f x) = (term48 _110796 _110799 r f x)) = ((term48 _110796 _110799 r f x) = (term49 _110796 _110799 r x f)).
Proof. exact (MK_COMB (@lem4810159 _110796 _110799 r f x) (@lem4810160 _110796 _110799 r x f)). Qed.
Lemma lem4810162 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term48 _110796 _110799 r f x) = (term49 _110796 _110799 r x f).
Proof. exact (EQ_MP (@lem4810161 _110796 _110799 r x f) (@lem4810153 _110796 _110799 r f x)). Qed.
Lemma lem4810167 {_110799 : Type'} (y : _110799) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4810168 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term53 _110796 _110799 r f x y) = (term54 _110796 _110799 r x f y).
Proof. exact (MK_COMB (@lem4810162 _110796 _110799 r x f) (@lem4810167 _110799 y)). Qed.
Lemma lem4810170 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4810171 {_110799 : Type'} (f : _110799 -> Prop) (y : _110799) : (term55 _110799 f y) = (f y).
Proof. exact (@lem4810170 _110799 Prop f y). Qed.
Lemma lem4810172 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term56 _110796 _110799 r x f y) = (term54 _110796 _110799 r x f y).
Proof. exact (@lem4810171 _110799 (term49 _110796 _110799 r x f) y). Qed.
Lemma lem4810173 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term54 _110796 _110799 r x f y) = (term57 _110796 _110799 r x f y).
Proof. exact (eq_refl (term54 _110796 _110799 r x f y)). Qed.
Lemma lem4810174 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term58 _110796 _110799 r x f) = (term49 _110796 _110799 r x f).
Proof. exact (fun_ext (fun y : _110799 => @lem4810173 _110796 _110799 r x f y)). Qed.
Lemma lem4810175 {_110799 : Type'} (y : _110799) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4810176 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term56 _110796 _110799 r x f y) = (term54 _110796 _110799 r x f y).
Proof. exact (MK_COMB (@lem4810174 _110796 _110799 r x f) (@lem4810175 _110799 y)). Qed.
Lemma lem4810177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4810178 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term59 _110796 _110799 r x f y) = (term60 _110796 _110799 r x f y).
Proof. exact (MK_COMB (@lem4810177) (@lem4810176 _110796 _110799 r x f y)). Qed.
Lemma lem4810179 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term54 _110796 _110799 r x f y) = (term57 _110796 _110799 r x f y).
Proof. exact (eq_refl (term54 _110796 _110799 r x f y)). Qed.
Lemma lem4810180 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : ((term56 _110796 _110799 r x f y) = (term54 _110796 _110799 r x f y)) = ((term54 _110796 _110799 r x f y) = (term57 _110796 _110799 r x f y)).
Proof. exact (MK_COMB (@lem4810178 _110796 _110799 r x f y) (@lem4810179 _110796 _110799 r x f y)). Qed.
Lemma lem4810181 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term54 _110796 _110799 r x f y) = (term57 _110796 _110799 r x f y).
Proof. exact (EQ_MP (@lem4810180 _110796 _110799 r x f y) (@lem4810172 _110796 _110799 r x f y)). Qed.
Lemma lem4810186 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term53 _110796 _110799 r f x y) = (term57 _110796 _110799 r x f y).
Proof. exact (TRANS (@lem4810168 _110796 _110799 r x f y) (@lem4810181 _110796 _110799 r x f y)). Qed.
Lemma lem4810187 {_110799 : Type'} (s : _110799 -> Prop) (x : _110799) (y : _110799) : (term61 _110799 s x y) = (term61 _110799 s x y).
Proof. exact (eq_refl (term61 _110799 s x y)). Qed.
Lemma lem4810188 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term62 _110796 _110799 s r f x y) = (term63 _110796 _110799 s r x f y).
Proof. exact (MK_COMB (@lem4810187 _110799 s x y) (@lem4810186 _110796 _110799 r x f y)). Qed.
Lemma lem4810191 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term64 _110796 _110799 s r f x) = (term65 _110796 _110799 s r x f).
Proof. exact (fun_ext (fun y : _110799 => @lem4810188 _110796 _110799 s r x f y)). Qed.
Lemma lem4810192 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4810193 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term66 _110796 _110799 s r f x) = (term67 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4810192 _110799) (@lem4810191 _110796 _110799 s r x f)). Qed.
Lemma lem4810198 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term68 _110796 _110799 s r f) = (term69 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4810193 _110796 _110799 s r x f)). Qed.
Lemma lem4810199 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4810200 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term43 _110796 _110799 s r f) = (term70 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4810199 _110799) (@lem4810198 _110796 _110799 s r f)). Qed.
Lemma lem4810205 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term42 _110796 _110799 r f s) = (term70 _110796 _110799 s r f).
Proof. exact (TRANS (@lem4810133 _110796 _110799 s r f) (@lem4810200 _110796 _110799 s r f)). Qed.
Lemma lem4810206 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term18 _110796 _110799 r f s) = (term42 _110796 _110799 r f s)) = ((term39 _110796 _110799 f s r) = (term70 _110796 _110799 s r f)).
Proof. exact (MK_COMB (@lem4810129 _110796 _110799 f s r) (@lem4810205 _110796 _110799 s r f)). Qed.
Lemma lem4810209 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) : (term71 _110796 _110799 r s) = (term72 _110796 _110799 s r).
Proof. exact (fun_ext (fun f : _110799 -> _110796 => @lem4810206 _110796 _110799 s r f)). Qed.
Lemma lem4810210 {_110796 _110799 : Type'} : (@all (_110799 -> _110796)) = (@all (_110799 -> _110796)).
Proof. exact (eq_refl (@all (_110799 -> _110796))). Qed.
Lemma lem4810211 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) : (term73 _110796 _110799 r s) = (term74 _110796 _110799 s r).
Proof. exact (MK_COMB (@lem4810210 _110796 _110799) (@lem4810209 _110796 _110799 s r)). Qed.
Lemma lem4810216 {_110796 _110799 : Type'} (s : _110799 -> Prop) : (term75 _110796 _110799 s) = (term76 _110796 _110799 s).
Proof. exact (fun_ext (fun r : type1402 _110796 => @lem4810211 _110796 _110799 s r)). Qed.
Lemma lem4810217 {_110796 : Type'} : (@all (_110796 -> _110796 -> Prop)) = (@all (_110796 -> _110796 -> Prop)).
Proof. exact (eq_refl (@all (_110796 -> _110796 -> Prop))). Qed.
Lemma lem4810218 {_110796 _110799 : Type'} (s : _110799 -> Prop) : (term77 _110796 _110799 s) = (term78 _110796 _110799 s).
Proof. exact (MK_COMB (@lem4810217 _110796) (@lem4810216 _110796 _110799 s)). Qed.
Lemma lem4810223 {_110796 _110799 : Type'} (s : _110799 -> Prop) : (term78 _110796 _110799 s) = (term77 _110796 _110799 s).
Proof. exact (SYM (@lem4810218 _110796 _110799 s)). Qed.
Lemma lem4810225 (p : Prop) : p = (term79 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4810226 {_110796 _110799 : Type'} (s : _110799 -> Prop) : (term78 _110796 _110799 s) = (term80 _110796 _110799 s).
Proof. exact (@lem4810225 (term78 _110796 _110799 s)). Qed.
Lemma lem4810227 {_110796 _110799 : Type'} (s : _110799 -> Prop) : (term80 _110796 _110799 s) = (term78 _110796 _110799 s).
Proof. exact (SYM (@lem4810226 _110796 _110799 s)). Qed.
Lemma lem4810228 {_110796 _110799 : Type'} (s : _110799 -> Prop) (h1 : term81 _110796 _110799 s) : term81 _110796 _110799 s.
Proof. exact (h1). Qed.
Lemma lem4810231 {_110796 _110799 : Type'} (s : _110799 -> Prop) (h1 : term80 _110796 _110799 s) : term80 _110796 _110799 s.
Proof. exact (h1). Qed.
Lemma lem4810232 {_110796 _110799 : Type'} (s : _110799 -> Prop) : term82 _110796 _110799 s.
Proof. exact (fun h0 : term80 _110796 _110799 s => @lem4810231 _110796 _110799 s h0). Qed.
Lemma lem4810233 {_110796 _110799 : Type'} (s : _110799 -> Prop) (h1 : term82 _110796 _110799 s) : term82 _110796 _110799 s.
Proof. exact (h1). Qed.
Lemma lem4810234 {_110796 _110799 : Type'} (s : _110799 -> Prop) (h1 : term80 _110796 _110799 s) : term80 _110796 _110799 s.
Proof. exact (h1). Qed.
Lemma lem4810235 {_110796 _110799 : Type'} (s : _110799 -> Prop) (h1 : term80 _110796 _110799 s) (h2 : term82 _110796 _110799 s) : term80 _110796 _110799 s.
Proof. exact (@lem4810233 _110796 _110799 s h2 (@lem4810234 _110796 _110799 s h1)). Qed.
Lemma lem4810236 {_110796 _110799 : Type'} (s : _110799 -> Prop) (h1 : term80 _110796 _110799 s) : term83 _110796 _110799 s.
Proof. exact (fun h0 : term82 _110796 _110799 s => @lem4810235 _110796 _110799 s h1 h0). Qed.
Lemma lem4810237 {_110796 _110799 : Type'} (s : _110799 -> Prop) (h1 : term82 _110796 _110799 s) : term82 _110796 _110799 s.
Proof. exact (h1). Qed.
Lemma lem4810238 {_110796 _110799 : Type'} (s : _110799 -> Prop) (h1 : term80 _110796 _110799 s) (h2 : term82 _110796 _110799 s) : term80 _110796 _110799 s.
Proof. exact (@lem4810236 _110796 _110799 s h1 (@lem4810237 _110796 _110799 s h2)). Qed.
Lemma lem4810239 {_110796 _110799 : Type'} (s : _110799 -> Prop) (h1 : term82 _110796 _110799 s) : term82 _110796 _110799 s.
Proof. exact (fun h0 : term80 _110796 _110799 s => @lem4810238 _110796 _110799 s h0 h1). Qed.
Lemma lem4810240 {_110796 _110799 : Type'} (s : _110799 -> Prop) : term84 _110796 _110799 s.
Proof. exact (fun h0 : term82 _110796 _110799 s => @lem4810239 _110796 _110799 s h0). Qed.
Lemma lem4810243 {_110796 _110799 : Type'} (s : _110799 -> Prop) : term82 _110796 _110799 s.
Proof. exact (@lem4810240 _110796 _110799 s (@lem4810232 _110796 _110799 s)). Qed.
Lemma lem4810244 {_110796 _110799 : Type'} (s : _110799 -> Prop) : term82 _110796 _110799 s.
Proof. exact (@lem4810243 _110796 _110799 s). Qed.
Lemma lem4810250 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4810251 {_110796 _110799 : Type'} (s : _110799 -> Prop) : (term80 _110796 _110799 s) = (term85 _110796 _110799 s).
Proof. exact (@lem4810250 (term81 _110796 _110799 s)). Qed.
Lemma lem4810253 (t : Prop) : (term86 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4810254 {_110796 _110799 : Type'} (s : _110799 -> Prop) : (term85 _110796 _110799 s) = (term78 _110796 _110799 s).
Proof. exact (@lem4810253 (term78 _110796 _110799 s)). Qed.
Lemma lem4810259 {_110796 _110799 : Type'} (s : _110799 -> Prop) : (term80 _110796 _110799 s) = (term78 _110796 _110799 s).
Proof. exact (TRANS (@lem4810251 _110796 _110799 s) (@lem4810254 _110796 _110799 s)). Qed.
Lemma lem4810394 {_110796 _110799 : Type'} : (term87 _110796 _110799) = (term88 _110796 _110799).
Proof. exact (fun_ext (fun s : _110799 -> Prop => @lem4810259 _110796 _110799 s)). Qed.
Lemma lem4810395 {_110799 : Type'} : (@all (_110799 -> Prop)) = (@all (_110799 -> Prop)).
Proof. exact (eq_refl (@all (_110799 -> Prop))). Qed.
Lemma lem4810404 {_110796 _110799 : Type'} : (term89 _110796 _110799) = (term90 _110796 _110799).
Proof. exact (MK_COMB (@lem4810395 _110799) (@lem4810394 _110796 _110799)). Qed.
Lemma lem4810425 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term63 _110796 _110799 s r x f y) = (term63 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term63 _110796 _110799 s r x f y)). Qed.
Lemma lem4810426 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term65 _110796 _110799 s r x f) = (term65 _110796 _110799 s r x f).
Proof. exact (fun_ext (fun y : _110799 => @lem4810425 _110796 _110799 s r x f y)). Qed.
Lemma lem4810427 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4810428 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term67 _110796 _110799 s r x f) = (term67 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4810427 _110799) (@lem4810426 _110796 _110799 s r x f)). Qed.
Lemma lem4810429 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term69 _110796 _110799 s r f) = (term69 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4810428 _110796 _110799 s r x f)). Qed.
Lemma lem4810430 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4810431 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term70 _110796 _110799 s r f) = (term70 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4810430 _110799) (@lem4810429 _110796 _110799 s r f)). Qed.
Lemma lem4810432 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4810435 {_110796 : Type'} (x : _110796) (y : _110796) : (term24 _110796 x y) = (term24 _110796 x y).
Proof. exact (eq_refl (term24 _110796 x y)). Qed.
Lemma lem4810440 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term91 _110796 _110799 y f x s) = (term91 _110796 _110799 y f x s).
Proof. exact (eq_refl (term91 _110796 _110799 y f x s)). Qed.
Lemma lem4810441 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term92 _110796 _110799 y f s) = (term92 _110796 _110799 y f s).
Proof. exact (fun_ext (fun x : _110799 => @lem4810440 _110796 _110799 y f x s)). Qed.
Lemma lem4810442 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4810443 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term21 _110796 _110799 y f s) = (term21 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4810442 _110799) (@lem4810441 _110796 _110799 y f s)). Qed.
Lemma lem4810444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4810445 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term23 _110796 _110799 y f s) = (term23 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4810444) (@lem4810443 _110796 _110799 y f s)). Qed.
Lemma lem4810446 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term26 _110796 _110799 f s x y) = (term26 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4810445 _110796 _110799 y f s) (@lem4810435 _110796 x y)). Qed.
Lemma lem4810451 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term91 _110796 _110799 x f x' s) = (term91 _110796 _110799 x f x' s).
Proof. exact (eq_refl (term91 _110796 _110799 x f x' s)). Qed.
Lemma lem4810452 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term92 _110796 _110799 x f s) = (term92 _110796 _110799 x f s).
Proof. exact (fun_ext (fun x' : _110799 => @lem4810451 _110796 _110799 x f x' s)). Qed.
Lemma lem4810453 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4810454 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term21 _110796 _110799 x f s) = (term21 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4810453 _110799) (@lem4810452 _110796 _110799 x f s)). Qed.
Lemma lem4810455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4810456 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term23 _110796 _110799 x f s) = (term23 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4810455) (@lem4810454 _110796 _110799 x f s)). Qed.
Lemma lem4810457 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term28 _110796 _110799 f s x y) = (term28 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4810456 _110796 _110799 x f s) (@lem4810446 _110796 _110799 f s x y)). Qed.
Lemma lem4810458 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4810459 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term30 _110796 _110799 f s x y) = (term30 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4810458) (@lem4810457 _110796 _110799 f s x y)). Qed.
Lemma lem4810460 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term32 _110796 _110799 f s r x y) = (term32 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4810459 _110796 _110799 f s x y) (@lem4810432 _110796 r x y)). Qed.
Lemma lem4810461 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term34 _110796 _110799 f s r x) = (term34 _110796 _110799 f s r x).
Proof. exact (fun_ext (fun y : _110796 => @lem4810460 _110796 _110799 f s r x y)). Qed.
Lemma lem4810462 {_110796 : Type'} : (@all _110796) = (@all _110796).
Proof. exact (eq_refl (@all _110796)). Qed.
Lemma lem4810463 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term36 _110796 _110799 f s r x) = (term36 _110796 _110799 f s r x).
Proof. exact (MK_COMB (@lem4810462 _110796) (@lem4810461 _110796 _110799 f s r x)). Qed.
Lemma lem4810464 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term38 _110796 _110799 f s r) = (term38 _110796 _110799 f s r).
Proof. exact (fun_ext (fun x : _110796 => @lem4810463 _110796 _110799 f s r x)). Qed.
Lemma lem4810465 {_110796 : Type'} : (@all _110796) = (@all _110796).
Proof. exact (eq_refl (@all _110796)). Qed.
Lemma lem4810466 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term39 _110796 _110799 f s r) = (term39 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4810465 _110796) (@lem4810464 _110796 _110799 f s r)). Qed.
Lemma lem4810467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4810468 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term41 _110796 _110799 f s r) = (term41 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4810467) (@lem4810466 _110796 _110799 f s r)). Qed.
Lemma lem4810469 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term39 _110796 _110799 f s r) = (term70 _110796 _110799 s r f)) = ((term39 _110796 _110799 f s r) = (term70 _110796 _110799 s r f)).
Proof. exact (MK_COMB (@lem4810468 _110796 _110799 f s r) (@lem4810431 _110796 _110799 s r f)). Qed.
Lemma lem4810470 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) : (term72 _110796 _110799 s r) = (term72 _110796 _110799 s r).
Proof. exact (fun_ext (fun f : _110799 -> _110796 => @lem4810469 _110796 _110799 s r f)). Qed.
Lemma lem4810471 {_110796 _110799 : Type'} : (@all (_110799 -> _110796)) = (@all (_110799 -> _110796)).
Proof. exact (eq_refl (@all (_110799 -> _110796))). Qed.
Lemma lem4810472 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) : (term74 _110796 _110799 s r) = (term74 _110796 _110799 s r).
Proof. exact (MK_COMB (@lem4810471 _110796 _110799) (@lem4810470 _110796 _110799 s r)). Qed.
Lemma lem4810473 {_110796 _110799 : Type'} (s : _110799 -> Prop) : (term76 _110796 _110799 s) = (term76 _110796 _110799 s).
Proof. exact (fun_ext (fun r : type1402 _110796 => @lem4810472 _110796 _110799 s r)). Qed.
Lemma lem4810474 {_110796 : Type'} : (@all (_110796 -> _110796 -> Prop)) = (@all (_110796 -> _110796 -> Prop)).
Proof. exact (eq_refl (@all (_110796 -> _110796 -> Prop))). Qed.
Lemma lem4810475 {_110796 _110799 : Type'} (s : _110799 -> Prop) : (term78 _110796 _110799 s) = (term78 _110796 _110799 s).
Proof. exact (MK_COMB (@lem4810474 _110796) (@lem4810473 _110796 _110799 s)). Qed.
Lemma lem4810476 {_110796 _110799 : Type'} : (term88 _110796 _110799) = (term88 _110796 _110799).
Proof. exact (fun_ext (fun s : _110799 -> Prop => @lem4810475 _110796 _110799 s)). Qed.
Lemma lem4810477 {_110799 : Type'} : (@all (_110799 -> Prop)) = (@all (_110799 -> Prop)).
Proof. exact (eq_refl (@all (_110799 -> Prop))). Qed.
Lemma lem4810478 {_110796 _110799 : Type'} : (term90 _110796 _110799) = (term90 _110796 _110799).
Proof. exact (MK_COMB (@lem4810477 _110799) (@lem4810476 _110796 _110799)). Qed.
Lemma lem4810553 {_110796 _110799 : Type'} : (term89 _110796 _110799) = (term90 _110796 _110799).
Proof. exact (TRANS (@lem4810404 _110796 _110799) (@lem4810478 _110796 _110799)). Qed.
Lemma lem4810554 {_110796 _110799 : Type'} : (term90 _110796 _110799) = (term89 _110796 _110799).
Proof. exact (SYM (@lem4810553 _110796 _110799)). Qed.
Lemma lem4810556 (p : Prop) : p = (term79 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4810557 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term39 _110796 _110799 f s r) = (term70 _110796 _110799 s r f)) = (term93 _110796 _110799 s r f).
Proof. exact (@lem4810556 ((term39 _110796 _110799 f s r) = (term70 _110796 _110799 s r f))). Qed.
Lemma lem4810558 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term93 _110796 _110799 s r f) = ((term39 _110796 _110799 f s r) = (term70 _110796 _110799 s r f)).
Proof. exact (SYM (@lem4810557 _110796 _110799 s r f)). Qed.
Lemma lem4810559 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term94 _110796 _110799 s r f) : term94 _110796 _110799 s r f.
Proof. exact (h1). Qed.
Lemma lem4810568 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term95 _110796 _110799 x f x' s) = (term96 _110796 _110799 x f x' s).
Proof. exact (@lem17045 (x = (f x')) (@IN _110799 x' s)). Qed.
Lemma lem4810571 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term91 _110796 _110799 x f x' s) = (term91 _110796 _110799 x f x' s).
Proof. exact (eq_refl (term91 _110796 _110799 x f x' s)). Qed.
Lemma lem4810572 {_110799 : Type'} (P : _110799 -> Prop) : (term97 _110799 P) = (term98 _110799 P).
Proof. exact (@lem18394 _110799 P). Qed.
Lemma lem4810573 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term99 _110796 _110799 x f s) = (term100 _110796 _110799 x f s).
Proof. exact (@lem4810572 _110799 (term92 _110796 _110799 x f s)). Qed.
Lemma lem4810574 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term101 _110796 _110799 x f s x') = (term91 _110796 _110799 x f x' s).
Proof. exact (eq_refl (term101 _110796 _110799 x f s x')). Qed.
Lemma lem4810575 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4810576 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term102 _110796 _110799 x f s x') = (term95 _110796 _110799 x f x' s).
Proof. exact (MK_COMB (@lem4810575) (@lem4810574 _110796 _110799 x f x' s)). Qed.
Lemma lem4810577 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term102 _110796 _110799 x f s x') = (term96 _110796 _110799 x f x' s).
Proof. exact (TRANS (@lem4810576 _110796 _110799 x f x' s) (@lem4810568 _110796 _110799 x f x' s)). Qed.
Lemma lem4810578 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term103 _110796 _110799 x f s) = (term104 _110796 _110799 x f s).
Proof. exact (fun_ext (fun x' : _110799 => @lem4810577 _110796 _110799 x f x' s)). Qed.
Lemma lem4810579 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4810580 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term100 _110796 _110799 x f s) = (term105 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4810579 _110799) (@lem4810578 _110796 _110799 x f s)). Qed.
Lemma lem4810581 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term99 _110796 _110799 x f s) = (term105 _110796 _110799 x f s).
Proof. exact (TRANS (@lem4810573 _110796 _110799 x f s) (@lem4810580 _110796 _110799 x f s)). Qed.
Lemma lem4810582 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term92 _110796 _110799 x f s) = (term92 _110796 _110799 x f s).
Proof. exact (fun_ext (fun x' : _110799 => @lem4810571 _110796 _110799 x f x' s)). Qed.
Lemma lem4810583 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4810584 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term21 _110796 _110799 x f s) = (term21 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4810583 _110799) (@lem4810582 _110796 _110799 x f s)). Qed.
Lemma lem4810593 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term95 _110796 _110799 y f x s) = (term96 _110796 _110799 y f x s).
Proof. exact (@lem17045 (y = (f x)) (@IN _110799 x s)). Qed.
Lemma lem4810596 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term91 _110796 _110799 y f x s) = (term91 _110796 _110799 y f x s).
Proof. exact (eq_refl (term91 _110796 _110799 y f x s)). Qed.
Lemma lem4810597 {_110799 : Type'} (P : _110799 -> Prop) : (term97 _110799 P) = (term98 _110799 P).
Proof. exact (@lem18394 _110799 P). Qed.
Lemma lem4810598 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term99 _110796 _110799 y f s) = (term100 _110796 _110799 y f s).
Proof. exact (@lem4810597 _110799 (term92 _110796 _110799 y f s)). Qed.
Lemma lem4810599 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term101 _110796 _110799 y f s x) = (term91 _110796 _110799 y f x s).
Proof. exact (eq_refl (term101 _110796 _110799 y f s x)). Qed.
Lemma lem4810600 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4810601 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term102 _110796 _110799 y f s x) = (term95 _110796 _110799 y f x s).
Proof. exact (MK_COMB (@lem4810600) (@lem4810599 _110796 _110799 y f x s)). Qed.
Lemma lem4810602 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term102 _110796 _110799 y f s x) = (term96 _110796 _110799 y f x s).
Proof. exact (TRANS (@lem4810601 _110796 _110799 y f x s) (@lem4810593 _110796 _110799 y f x s)). Qed.
Lemma lem4810603 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term103 _110796 _110799 y f s) = (term104 _110796 _110799 y f s).
Proof. exact (fun_ext (fun x : _110799 => @lem4810602 _110796 _110799 y f x s)). Qed.
Lemma lem4810604 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4810605 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term100 _110796 _110799 y f s) = (term105 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4810604 _110799) (@lem4810603 _110796 _110799 y f s)). Qed.
Lemma lem4810606 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term99 _110796 _110799 y f s) = (term105 _110796 _110799 y f s).
Proof. exact (TRANS (@lem4810598 _110796 _110799 y f s) (@lem4810605 _110796 _110799 y f s)). Qed.
Lemma lem4810607 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term92 _110796 _110799 y f s) = (term92 _110796 _110799 y f s).
Proof. exact (fun_ext (fun x : _110799 => @lem4810596 _110796 _110799 y f x s)). Qed.
Lemma lem4810608 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4810609 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term21 _110796 _110799 y f s) = (term21 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4810608 _110799) (@lem4810607 _110796 _110799 y f s)). Qed.
Lemma lem4810610 {_110796 : Type'} (x : _110796) (y : _110796) : (term24 _110796 x y) = (term24 _110796 x y).
Proof. exact (eq_refl (term24 _110796 x y)). Qed.
Lemma lem4810613 {_110796 : Type'} (x : _110796) (y : _110796) : (term106 _110796 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4810614 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4810615 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term107 _110796 _110799 y f s) = (term108 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4810614) (@lem4810606 _110796 _110799 y f s)). Qed.
Lemma lem4810616 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term109 _110796 _110799 f s x y) = (term110 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4810615 _110796 _110799 y f s) (@lem4810613 _110796 x y)). Qed.
Lemma lem4810617 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term111 _110796 _110799 f s x y) = (term109 _110796 _110799 f s x y).
Proof. exact (@lem17045 (term21 _110796 _110799 y f s) (term24 _110796 x y)). Qed.
Lemma lem4810618 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term111 _110796 _110799 f s x y) = (term110 _110796 _110799 f s x y).
Proof. exact (TRANS (@lem4810617 _110796 _110799 f s x y) (@lem4810616 _110796 _110799 f s x y)). Qed.
Lemma lem4810619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4810620 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term23 _110796 _110799 y f s) = (term23 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4810619) (@lem4810609 _110796 _110799 y f s)). Qed.
Lemma lem4810621 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term26 _110796 _110799 f s x y) = (term26 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4810620 _110796 _110799 y f s) (@lem4810610 _110796 x y)). Qed.
Lemma lem4810622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4810623 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term107 _110796 _110799 x f s) = (term108 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4810622) (@lem4810581 _110796 _110799 x f s)). Qed.
Lemma lem4810624 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term112 _110796 _110799 f s x y) = (term113 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4810623 _110796 _110799 x f s) (@lem4810618 _110796 _110799 f s x y)). Qed.
Lemma lem4810625 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term114 _110796 _110799 f s x y) = (term112 _110796 _110799 f s x y).
Proof. exact (@lem17045 (term21 _110796 _110799 x f s) (term26 _110796 _110799 f s x y)). Qed.
Lemma lem4810626 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term114 _110796 _110799 f s x y) = (term113 _110796 _110799 f s x y).
Proof. exact (TRANS (@lem4810625 _110796 _110799 f s x y) (@lem4810624 _110796 _110799 f s x y)). Qed.
Lemma lem4810627 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4810628 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term23 _110796 _110799 x f s) = (term23 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4810627) (@lem4810584 _110796 _110799 x f s)). Qed.
Lemma lem4810629 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term28 _110796 _110799 f s x y) = (term28 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4810628 _110796 _110799 x f s) (@lem4810621 _110796 _110799 f s x y)). Qed.
Lemma lem4810630 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (term115 _110796 r x y) = (term115 _110796 r x y).
Proof. exact (eq_refl (term115 _110796 r x y)). Qed.
Lemma lem4810631 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4810632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4810633 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term116 _110796 _110799 f s x y) = (term116 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4810632) (@lem4810629 _110796 _110799 f s x y)). Qed.
Lemma lem4810634 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term117 _110796 _110799 f s r x y) = (term117 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4810633 _110796 _110799 f s x y) (@lem4810630 _110796 r x y)). Qed.
Lemma lem4810635 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term118 _110796 _110799 f s r x y) = (term117 _110796 _110799 f s r x y).
Proof. exact (@lem17362 (term28 _110796 _110799 f s x y) (r x y)). Qed.
Lemma lem4810636 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term118 _110796 _110799 f s r x y) = (term117 _110796 _110799 f s r x y).
Proof. exact (TRANS (@lem4810635 _110796 _110799 f s r x y) (@lem4810634 _110796 _110799 f s r x y)). Qed.
Lemma lem4810637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4810638 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term119 _110796 _110799 f s x y) = (term120 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4810637) (@lem4810626 _110796 _110799 f s x y)). Qed.
Lemma lem4810639 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term121 _110796 _110799 f s r x y) = (term122 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4810638 _110796 _110799 f s x y) (@lem4810631 _110796 r x y)). Qed.
Lemma lem4810640 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term32 _110796 _110799 f s r x y) = (term121 _110796 _110799 f s r x y).
Proof. exact (@lem17265 (term28 _110796 _110799 f s x y) (r x y)). Qed.
Lemma lem4810641 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term32 _110796 _110799 f s r x y) = (term122 _110796 _110799 f s r x y).
Proof. exact (TRANS (@lem4810640 _110796 _110799 f s r x y) (@lem4810639 _110796 _110799 f s r x y)). Qed.
Lemma lem4810642 {_110796 : Type'} (P : _110796 -> Prop) : (term123 _110796 P) = (term124 _110796 P).
Proof. exact (@lem18392 _110796 P). Qed.
Lemma lem4810643 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term125 _110796 _110799 f s r x) = (term126 _110796 _110799 f s r x).
Proof. exact (@lem4810642 _110796 (term34 _110796 _110799 f s r x)). Qed.
Lemma lem4810644 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term127 _110796 _110799 f s r x y) = (term32 _110796 _110799 f s r x y).
Proof. exact (eq_refl (term127 _110796 _110799 f s r x y)). Qed.
Lemma lem4810645 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4810646 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term128 _110796 _110799 f s r x y) = (term118 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4810645) (@lem4810644 _110796 _110799 f s r x y)). Qed.
Lemma lem4810647 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term128 _110796 _110799 f s r x y) = (term117 _110796 _110799 f s r x y).
Proof. exact (TRANS (@lem4810646 _110796 _110799 f s r x y) (@lem4810636 _110796 _110799 f s r x y)). Qed.
Lemma lem4810648 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term129 _110796 _110799 f s r x) = (term130 _110796 _110799 f s r x).
Proof. exact (fun_ext (fun y : _110796 => @lem4810647 _110796 _110799 f s r x y)). Qed.
Lemma lem4810649 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4810650 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term126 _110796 _110799 f s r x) = (term131 _110796 _110799 f s r x).
Proof. exact (MK_COMB (@lem4810649 _110796) (@lem4810648 _110796 _110799 f s r x)). Qed.
Lemma lem4810651 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term125 _110796 _110799 f s r x) = (term131 _110796 _110799 f s r x).
Proof. exact (TRANS (@lem4810643 _110796 _110799 f s r x) (@lem4810650 _110796 _110799 f s r x)). Qed.
Lemma lem4810652 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term34 _110796 _110799 f s r x) = (term132 _110796 _110799 f s r x).
Proof. exact (fun_ext (fun y : _110796 => @lem4810641 _110796 _110799 f s r x y)). Qed.
Lemma lem4810653 {_110796 : Type'} : (@all _110796) = (@all _110796).
Proof. exact (eq_refl (@all _110796)). Qed.
Lemma lem4810654 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term36 _110796 _110799 f s r x) = (term133 _110796 _110799 f s r x).
Proof. exact (MK_COMB (@lem4810653 _110796) (@lem4810652 _110796 _110799 f s r x)). Qed.
Lemma lem4810655 {_110796 : Type'} (P : _110796 -> Prop) : (term123 _110796 P) = (term124 _110796 P).
Proof. exact (@lem18392 _110796 P). Qed.
Lemma lem4810656 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term134 _110796 _110799 f s r) = (term135 _110796 _110799 f s r).
Proof. exact (@lem4810655 _110796 (term38 _110796 _110799 f s r)). Qed.
Lemma lem4810657 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term136 _110796 _110799 f s r x) = (term36 _110796 _110799 f s r x).
Proof. exact (eq_refl (term136 _110796 _110799 f s r x)). Qed.
Lemma lem4810658 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4810659 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term137 _110796 _110799 f s r x) = (term125 _110796 _110799 f s r x).
Proof. exact (MK_COMB (@lem4810658) (@lem4810657 _110796 _110799 f s r x)). Qed.
Lemma lem4810660 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term137 _110796 _110799 f s r x) = (term131 _110796 _110799 f s r x).
Proof. exact (TRANS (@lem4810659 _110796 _110799 f s r x) (@lem4810651 _110796 _110799 f s r x)). Qed.
Lemma lem4810661 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term138 _110796 _110799 f s r) = (term139 _110796 _110799 f s r).
Proof. exact (fun_ext (fun x : _110796 => @lem4810660 _110796 _110799 f s r x)). Qed.
Lemma lem4810662 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4810663 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term135 _110796 _110799 f s r) = (term140 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4810662 _110796) (@lem4810661 _110796 _110799 f s r)). Qed.
Lemma lem4810664 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term134 _110796 _110799 f s r) = (term140 _110796 _110799 f s r).
Proof. exact (TRANS (@lem4810656 _110796 _110799 f s r) (@lem4810663 _110796 _110799 f s r)). Qed.
Lemma lem4810665 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term38 _110796 _110799 f s r) = (term141 _110796 _110799 f s r).
Proof. exact (fun_ext (fun x : _110796 => @lem4810654 _110796 _110799 f s r x)). Qed.
Lemma lem4810666 {_110796 : Type'} : (@all _110796) = (@all _110796).
Proof. exact (eq_refl (@all _110796)). Qed.
Lemma lem4810667 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term39 _110796 _110799 f s r) = (term142 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4810666 _110796) (@lem4810665 _110796 _110799 f s r)). Qed.
Lemma lem4810675 {_110799 : Type'} (x : _110799) (y : _110799) : (term106 _110799 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4810677 {_110799 : Type'} (y : _110799) (s : _110799 -> Prop) : (term143 _110799 y s) = (term143 _110799 y s).
Proof. exact (eq_refl (term143 _110799 y s)). Qed.
Lemma lem4810678 {_110799 : Type'} (s : _110799 -> Prop) (x : _110799) (y : _110799) : (term144 _110799 s x y) = (term145 _110799 s x y).
Proof. exact (MK_COMB (@lem4810677 _110799 y s) (@lem4810675 _110799 x y)). Qed.
Lemma lem4810679 {_110799 : Type'} (s : _110799 -> Prop) (x : _110799) (y : _110799) : (term146 _110799 s x y) = (term144 _110799 s x y).
Proof. exact (@lem17045 (@IN _110799 y s) (term24 _110799 x y)). Qed.
Lemma lem4810680 {_110799 : Type'} (s : _110799 -> Prop) (x : _110799) (y : _110799) : (term146 _110799 s x y) = (term145 _110799 s x y).
Proof. exact (TRANS (@lem4810679 _110799 s x y) (@lem4810678 _110799 s x y)). Qed.
Lemma lem4810685 {_110799 : Type'} (x : _110799) (s : _110799 -> Prop) : (term143 _110799 x s) = (term143 _110799 x s).
Proof. exact (eq_refl (term143 _110799 x s)). Qed.
Lemma lem4810686 {_110799 : Type'} (s : _110799 -> Prop) (x : _110799) (y : _110799) : (term147 _110799 s x y) = (term148 _110799 s x y).
Proof. exact (MK_COMB (@lem4810685 _110799 x s) (@lem4810680 _110799 s x y)). Qed.
Lemma lem4810687 {_110799 : Type'} (s : _110799 -> Prop) (x : _110799) (y : _110799) : (term149 _110799 s x y) = (term147 _110799 s x y).
Proof. exact (@lem17045 (@IN _110799 x s) (term150 _110799 s x y)). Qed.
Lemma lem4810688 {_110799 : Type'} (s : _110799 -> Prop) (x : _110799) (y : _110799) : (term149 _110799 s x y) = (term148 _110799 s x y).
Proof. exact (TRANS (@lem4810687 _110799 s x y) (@lem4810686 _110799 s x y)). Qed.
Lemma lem4810695 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term151 _110796 _110799 x f y) = ((f x) = (f y)).
Proof. exact (@lem16933 ((f x) = (f y))). Qed.
Lemma lem4810697 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term152 _110796 _110799 r x f y) = (term152 _110796 _110799 r x f y).
Proof. exact (eq_refl (term152 _110796 _110799 r x f y)). Qed.
Lemma lem4810702 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term153 _110796 _110799 r x f y) = (term154 _110796 _110799 r x f y).
Proof. exact (@lem17362 (term155 _110796 _110799 x f y) (term152 _110796 _110799 r x f y)). Qed.
Lemma lem4810703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4810704 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term156 _110796 _110799 x f y) = (term157 _110796 _110799 x f y).
Proof. exact (MK_COMB (@lem4810703) (@lem4810695 _110796 _110799 x f y)). Qed.
Lemma lem4810705 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term158 _110796 _110799 r x f y) = (term159 _110796 _110799 r x f y).
Proof. exact (MK_COMB (@lem4810704 _110796 _110799 x f y) (@lem4810697 _110796 _110799 r x f y)). Qed.
Lemma lem4810706 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term57 _110796 _110799 r x f y) = (term158 _110796 _110799 r x f y).
Proof. exact (@lem17265 (term155 _110796 _110799 x f y) (term152 _110796 _110799 r x f y)). Qed.
Lemma lem4810707 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term57 _110796 _110799 r x f y) = (term159 _110796 _110799 r x f y).
Proof. exact (TRANS (@lem4810706 _110796 _110799 r x f y) (@lem4810705 _110796 _110799 r x f y)). Qed.
Lemma lem4810709 {_110799 : Type'} (s : _110799 -> Prop) (x : _110799) (y : _110799) : (term160 _110799 s x y) = (term160 _110799 s x y).
Proof. exact (eq_refl (term160 _110799 s x y)). Qed.
Lemma lem4810710 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term161 _110796 _110799 s r x f y) = (term162 _110796 _110799 s r x f y).
Proof. exact (MK_COMB (@lem4810709 _110799 s x y) (@lem4810702 _110796 _110799 r x f y)). Qed.
Lemma lem4810711 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term163 _110796 _110799 s r x f y) = (term161 _110796 _110799 s r x f y).
Proof. exact (@lem17362 (term164 _110799 s x y) (term57 _110796 _110799 r x f y)). Qed.
Lemma lem4810712 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term163 _110796 _110799 s r x f y) = (term162 _110796 _110799 s r x f y).
Proof. exact (TRANS (@lem4810711 _110796 _110799 s r x f y) (@lem4810710 _110796 _110799 s r x f y)). Qed.
Lemma lem4810713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4810714 {_110799 : Type'} (s : _110799 -> Prop) (x : _110799) (y : _110799) : (term165 _110799 s x y) = (term166 _110799 s x y).
Proof. exact (MK_COMB (@lem4810713) (@lem4810688 _110799 s x y)). Qed.
Lemma lem4810715 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term167 _110796 _110799 s r x f y) = (term168 _110796 _110799 s r x f y).
Proof. exact (MK_COMB (@lem4810714 _110799 s x y) (@lem4810707 _110796 _110799 r x f y)). Qed.
Lemma lem4810716 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term63 _110796 _110799 s r x f y) = (term167 _110796 _110799 s r x f y).
Proof. exact (@lem17265 (term164 _110799 s x y) (term57 _110796 _110799 r x f y)). Qed.
Lemma lem4810717 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term63 _110796 _110799 s r x f y) = (term168 _110796 _110799 s r x f y).
Proof. exact (TRANS (@lem4810716 _110796 _110799 s r x f y) (@lem4810715 _110796 _110799 s r x f y)). Qed.
Lemma lem4810718 {_110799 : Type'} (P : _110799 -> Prop) : (term123 _110799 P) = (term124 _110799 P).
Proof. exact (@lem18392 _110799 P). Qed.
Lemma lem4810719 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term169 _110796 _110799 s r x f) = (term170 _110796 _110799 s r x f).
Proof. exact (@lem4810718 _110799 (term65 _110796 _110799 s r x f)). Qed.
Lemma lem4810720 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term171 _110796 _110799 s r x f y) = (term63 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term171 _110796 _110799 s r x f y)). Qed.
Lemma lem4810721 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4810722 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term172 _110796 _110799 s r x f y) = (term163 _110796 _110799 s r x f y).
Proof. exact (MK_COMB (@lem4810721) (@lem4810720 _110796 _110799 s r x f y)). Qed.
Lemma lem4810723 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term172 _110796 _110799 s r x f y) = (term162 _110796 _110799 s r x f y).
Proof. exact (TRANS (@lem4810722 _110796 _110799 s r x f y) (@lem4810712 _110796 _110799 s r x f y)). Qed.
Lemma lem4810724 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term173 _110796 _110799 s r x f) = (term174 _110796 _110799 s r x f).
Proof. exact (fun_ext (fun y : _110799 => @lem4810723 _110796 _110799 s r x f y)). Qed.
Lemma lem4810725 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4810726 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term170 _110796 _110799 s r x f) = (term175 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4810725 _110799) (@lem4810724 _110796 _110799 s r x f)). Qed.
Lemma lem4810727 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term169 _110796 _110799 s r x f) = (term175 _110796 _110799 s r x f).
Proof. exact (TRANS (@lem4810719 _110796 _110799 s r x f) (@lem4810726 _110796 _110799 s r x f)). Qed.
Lemma lem4810728 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term65 _110796 _110799 s r x f) = (term176 _110796 _110799 s r x f).
Proof. exact (fun_ext (fun y : _110799 => @lem4810717 _110796 _110799 s r x f y)). Qed.
Lemma lem4810729 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4810730 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term67 _110796 _110799 s r x f) = (term177 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4810729 _110799) (@lem4810728 _110796 _110799 s r x f)). Qed.
Lemma lem4810731 {_110799 : Type'} (P : _110799 -> Prop) : (term123 _110799 P) = (term124 _110799 P).
Proof. exact (@lem18392 _110799 P). Qed.
Lemma lem4810732 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term178 _110796 _110799 s r f) = (term179 _110796 _110799 s r f).
Proof. exact (@lem4810731 _110799 (term69 _110796 _110799 s r f)). Qed.
Lemma lem4810733 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term180 _110796 _110799 s r f x) = (term67 _110796 _110799 s r x f).
Proof. exact (eq_refl (term180 _110796 _110799 s r f x)). Qed.
Lemma lem4810734 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4810735 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term181 _110796 _110799 s r f x) = (term169 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4810734) (@lem4810733 _110796 _110799 s r x f)). Qed.
Lemma lem4810736 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term181 _110796 _110799 s r f x) = (term175 _110796 _110799 s r x f).
Proof. exact (TRANS (@lem4810735 _110796 _110799 s r x f) (@lem4810727 _110796 _110799 s r x f)). Qed.
Lemma lem4810737 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term182 _110796 _110799 s r f) = (term183 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4810736 _110796 _110799 s r x f)). Qed.
Lemma lem4810738 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4810739 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term179 _110796 _110799 s r f) = (term184 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4810738 _110799) (@lem4810737 _110796 _110799 s r f)). Qed.
Lemma lem4810740 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term178 _110796 _110799 s r f) = (term184 _110796 _110799 s r f).
Proof. exact (TRANS (@lem4810732 _110796 _110799 s r f) (@lem4810739 _110796 _110799 s r f)). Qed.
Lemma lem4810741 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term69 _110796 _110799 s r f) = (term185 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4810730 _110796 _110799 s r x f)). Qed.
Lemma lem4810742 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4810743 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term70 _110796 _110799 s r f) = (term186 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4810742 _110799) (@lem4810741 _110796 _110799 s r f)). Qed.
Lemma lem4810744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4810745 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term187 _110796 _110799 f s r) = (term188 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4810744) (@lem4810664 _110796 _110799 f s r)). Qed.
Lemma lem4810746 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term189 _110796 _110799 s r f) = (term190 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4810745 _110796 _110799 f s r) (@lem4810743 _110796 _110799 s r f)). Qed.
Lemma lem4810747 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4810748 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term191 _110796 _110799 f s r) = (term192 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4810747) (@lem4810667 _110796 _110799 f s r)). Qed.
Lemma lem4810749 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term193 _110796 _110799 s r f) = (term194 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4810748 _110796 _110799 f s r) (@lem4810740 _110796 _110799 s r f)). Qed.
Lemma lem4810750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4810751 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term195 _110796 _110799 s r f) = (term196 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4810750) (@lem4810749 _110796 _110799 s r f)). Qed.
Lemma lem4810752 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term197 _110796 _110799 s r f) = (term198 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4810751 _110796 _110799 s r f) (@lem4810746 _110796 _110799 s r f)). Qed.
Lemma lem4810753 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term94 _110796 _110799 s r f) = (term197 _110796 _110799 s r f).
Proof. exact (@lem17646 (term39 _110796 _110799 f s r) (term70 _110796 _110799 s r f)). Qed.
Lemma lem4810754 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term94 _110796 _110799 s r f) = (term198 _110796 _110799 s r f).
Proof. exact (TRANS (@lem4810753 _110796 _110799 s r f) (@lem4810752 _110796 _110799 s r f)). Qed.
Lemma lem4811157 {A : Type'} (P : Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4811158 {_110799 : Type'} (P : Prop) (Q : _110799 -> Prop) : (term199 _110799 P Q) = (term200 _110799 P Q).
Proof. exact (@lem4811157 _110799 P Q). Qed.
Lemma lem4811159 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term201 _110796 _110799 s r f) = (term202 _110796 _110799 s r f).
Proof. exact (@lem4811158 _110799 (term142 _110796 _110799 f s r) (term183 _110796 _110799 s r f)). Qed.
Lemma lem4811160 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term203 _110796 _110799 s r f x) = (term175 _110796 _110799 s r x f).
Proof. exact (eq_refl (term203 _110796 _110799 s r f x)). Qed.
Lemma lem4811161 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term204 _110796 _110799 s r f) = (term183 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4811160 _110796 _110799 s r x f)). Qed.
Lemma lem4811162 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811163 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term205 _110796 _110799 s r f) = (term184 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811162 _110799) (@lem4811161 _110796 _110799 s r f)). Qed.
Lemma lem4811164 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term192 _110796 _110799 f s r) = (term192 _110796 _110799 f s r).
Proof. exact (eq_refl (term192 _110796 _110799 f s r)). Qed.
Lemma lem4811165 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term201 _110796 _110799 s r f) = (term194 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811164 _110796 _110799 f s r) (@lem4811163 _110796 _110799 s r f)). Qed.
Lemma lem4811166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811167 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term206 _110796 _110799 s r f) = (term207 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811166) (@lem4811165 _110796 _110799 s r f)). Qed.
Lemma lem4811168 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term203 _110796 _110799 s r f x) = (term175 _110796 _110799 s r x f).
Proof. exact (eq_refl (term203 _110796 _110799 s r f x)). Qed.
Lemma lem4811169 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term192 _110796 _110799 f s r) = (term192 _110796 _110799 f s r).
Proof. exact (eq_refl (term192 _110796 _110799 f s r)). Qed.
Lemma lem4811170 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term208 _110796 _110799 s r f x) = (term209 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4811169 _110796 _110799 f s r) (@lem4811168 _110796 _110799 s r x f)). Qed.
Lemma lem4811171 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term210 _110796 _110799 s r f) = (term211 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4811170 _110796 _110799 s r x f)). Qed.
Lemma lem4811172 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811173 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term202 _110796 _110799 s r f) = (term212 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811172 _110799) (@lem4811171 _110796 _110799 s r f)). Qed.
Lemma lem4811174 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term201 _110796 _110799 s r f) = (term202 _110796 _110799 s r f)) = ((term194 _110796 _110799 s r f) = (term212 _110796 _110799 s r f)).
Proof. exact (MK_COMB (@lem4811167 _110796 _110799 s r f) (@lem4811173 _110796 _110799 s r f)). Qed.
Lemma lem4811175 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term194 _110796 _110799 s r f) = (term212 _110796 _110799 s r f).
Proof. exact (EQ_MP (@lem4811174 _110796 _110799 s r f) (@lem4811159 _110796 _110799 s r f)). Qed.
Lemma lem4811177 {A : Type'} (P : Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4811178 {_110799 : Type'} (P : Prop) (Q : _110799 -> Prop) : (term199 _110799 P Q) = (term200 _110799 P Q).
Proof. exact (@lem4811177 _110799 P Q). Qed.
Lemma lem4811179 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term213 _110796 _110799 s r x f) = (term214 _110796 _110799 s r x f).
Proof. exact (@lem4811178 _110799 (term142 _110796 _110799 f s r) (term174 _110796 _110799 s r x f)). Qed.
Lemma lem4811180 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term215 _110796 _110799 s r x f y) = (term162 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term215 _110796 _110799 s r x f y)). Qed.
Lemma lem4811181 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term216 _110796 _110799 s r x f) = (term174 _110796 _110799 s r x f).
Proof. exact (fun_ext (fun y : _110799 => @lem4811180 _110796 _110799 s r x f y)). Qed.
Lemma lem4811182 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811183 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term217 _110796 _110799 s r x f) = (term175 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4811182 _110799) (@lem4811181 _110796 _110799 s r x f)). Qed.
Lemma lem4811184 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term192 _110796 _110799 f s r) = (term192 _110796 _110799 f s r).
Proof. exact (eq_refl (term192 _110796 _110799 f s r)). Qed.
Lemma lem4811185 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term213 _110796 _110799 s r x f) = (term209 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4811184 _110796 _110799 f s r) (@lem4811183 _110796 _110799 s r x f)). Qed.
Lemma lem4811186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811187 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term218 _110796 _110799 s r x f) = (term219 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4811186) (@lem4811185 _110796 _110799 s r x f)). Qed.
Lemma lem4811188 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term215 _110796 _110799 s r x f y) = (term162 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term215 _110796 _110799 s r x f y)). Qed.
Lemma lem4811189 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term192 _110796 _110799 f s r) = (term192 _110796 _110799 f s r).
Proof. exact (eq_refl (term192 _110796 _110799 f s r)). Qed.
Lemma lem4811190 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term220 _110796 _110799 s r x f y) = (term221 _110796 _110799 s r x f y).
Proof. exact (MK_COMB (@lem4811189 _110796 _110799 f s r) (@lem4811188 _110796 _110799 s r x f y)). Qed.
Lemma lem4811191 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term222 _110796 _110799 s r x f) = (term223 _110796 _110799 s r x f).
Proof. exact (fun_ext (fun y : _110799 => @lem4811190 _110796 _110799 s r x f y)). Qed.
Lemma lem4811192 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811193 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term214 _110796 _110799 s r x f) = (term224 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4811192 _110799) (@lem4811191 _110796 _110799 s r x f)). Qed.
Lemma lem4811194 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : ((term213 _110796 _110799 s r x f) = (term214 _110796 _110799 s r x f)) = ((term209 _110796 _110799 s r x f) = (term224 _110796 _110799 s r x f)).
Proof. exact (MK_COMB (@lem4811187 _110796 _110799 s r x f) (@lem4811193 _110796 _110799 s r x f)). Qed.
Lemma lem4811195 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term209 _110796 _110799 s r x f) = (term224 _110796 _110799 s r x f).
Proof. exact (EQ_MP (@lem4811194 _110796 _110799 s r x f) (@lem4811179 _110796 _110799 s r x f)). Qed.
Lemma lem4811196 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term211 _110796 _110799 s r f) = (term225 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4811195 _110796 _110799 s r x f)). Qed.
Lemma lem4811197 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811198 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term212 _110796 _110799 s r f) = (term226 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811197 _110799) (@lem4811196 _110796 _110799 s r f)). Qed.
Lemma lem4811199 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term194 _110796 _110799 s r f) = (term226 _110796 _110799 s r f).
Proof. exact (TRANS (@lem4811175 _110796 _110799 s r f) (@lem4811198 _110796 _110799 s r f)). Qed.
Lemma lem4811200 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811201 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term196 _110796 _110799 s r f) = (term227 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811200) (@lem4811199 _110796 _110799 s r f)). Qed.
Lemma lem4811203 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4811204 {_110799 : Type'} (P : _110799 -> Prop) (Q : Prop) : (term228 _110799 P Q) = (term229 _110799 P Q).
Proof. exact (@lem4811203 _110799 P Q). Qed.
Lemma lem4811205 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term230 _110796 _110799 f s x y) = (term231 _110796 _110799 f s x y).
Proof. exact (@lem4811204 _110799 (term92 _110796 _110799 y f s) (term24 _110796 x y)). Qed.
Lemma lem4811206 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term101 _110796 _110799 y f s x) = (term91 _110796 _110799 y f x s).
Proof. exact (eq_refl (term101 _110796 _110799 y f s x)). Qed.
Lemma lem4811207 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term232 _110796 _110799 y f s) = (term92 _110796 _110799 y f s).
Proof. exact (fun_ext (fun x : _110799 => @lem4811206 _110796 _110799 y f x s)). Qed.
Lemma lem4811208 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811209 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term233 _110796 _110799 y f s) = (term21 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4811208 _110799) (@lem4811207 _110796 _110799 y f s)). Qed.
Lemma lem4811210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811211 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term234 _110796 _110799 y f s) = (term23 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4811210) (@lem4811209 _110796 _110799 y f s)). Qed.
Lemma lem4811212 {_110796 : Type'} (x : _110796) (y : _110796) : (term24 _110796 x y) = (term24 _110796 x y).
Proof. exact (eq_refl (term24 _110796 x y)). Qed.
Lemma lem4811213 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term230 _110796 _110799 f s x y) = (term26 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811211 _110796 _110799 y f s) (@lem4811212 _110796 x y)). Qed.
Lemma lem4811214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811215 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term235 _110796 _110799 f s x y) = (term236 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811214) (@lem4811213 _110796 _110799 f s x y)). Qed.
Lemma lem4811216 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term101 _110796 _110799 y f s x) = (term91 _110796 _110799 y f x s).
Proof. exact (eq_refl (term101 _110796 _110799 y f s x)). Qed.
Lemma lem4811217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811218 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term237 _110796 _110799 y f s x) = (term238 _110796 _110799 y f x s).
Proof. exact (MK_COMB (@lem4811217) (@lem4811216 _110796 _110799 y f x s)). Qed.
Lemma lem4811219 {_110796 : Type'} (x : _110796) (y : _110796) : (term24 _110796 x y) = (term24 _110796 x y).
Proof. exact (eq_refl (term24 _110796 x y)). Qed.
Lemma lem4811220 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term239 _110796 _110799 f s x x' y) = (term240 _110796 _110799 f x s x' y).
Proof. exact (MK_COMB (@lem4811218 _110796 _110799 y f x s) (@lem4811219 _110796 x' y)). Qed.
Lemma lem4811221 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term241 _110796 _110799 f s x y) = (term242 _110796 _110799 f s x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811220 _110796 _110799 f x' s x y)). Qed.
Lemma lem4811222 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811223 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term231 _110796 _110799 f s x y) = (term243 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811222 _110799) (@lem4811221 _110796 _110799 f s x y)). Qed.
Lemma lem4811224 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : ((term230 _110796 _110799 f s x y) = (term231 _110796 _110799 f s x y)) = ((term26 _110796 _110799 f s x y) = (term243 _110796 _110799 f s x y)).
Proof. exact (MK_COMB (@lem4811215 _110796 _110799 f s x y) (@lem4811223 _110796 _110799 f s x y)). Qed.
Lemma lem4811225 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term26 _110796 _110799 f s x y) = (term243 _110796 _110799 f s x y).
Proof. exact (EQ_MP (@lem4811224 _110796 _110799 f s x y) (@lem4811205 _110796 _110799 f s x y)). Qed.
Lemma lem4811226 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term23 _110796 _110799 x f s) = (term23 _110796 _110799 x f s).
Proof. exact (eq_refl (term23 _110796 _110799 x f s)). Qed.
Lemma lem4811227 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term28 _110796 _110799 f s x y) = (term244 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811226 _110796 _110799 x f s) (@lem4811225 _110796 _110799 f s x y)). Qed.
Lemma lem4811229 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4811230 {_110799 : Type'} (P : _110799 -> Prop) (Q : Prop) : (term228 _110799 P Q) = (term229 _110799 P Q).
Proof. exact (@lem4811229 _110799 P Q). Qed.
Lemma lem4811231 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term245 _110796 _110799 f s x y) = (term246 _110796 _110799 f s x y).
Proof. exact (@lem4811230 _110799 (term92 _110796 _110799 x f s) (term243 _110796 _110799 f s x y)). Qed.
Lemma lem4811232 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term101 _110796 _110799 x f s x') = (term91 _110796 _110799 x f x' s).
Proof. exact (eq_refl (term101 _110796 _110799 x f s x')). Qed.
Lemma lem4811233 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term232 _110796 _110799 x f s) = (term92 _110796 _110799 x f s).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811232 _110796 _110799 x f x' s)). Qed.
Lemma lem4811234 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811235 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term233 _110796 _110799 x f s) = (term21 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4811234 _110799) (@lem4811233 _110796 _110799 x f s)). Qed.
Lemma lem4811236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811237 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term234 _110796 _110799 x f s) = (term23 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4811236) (@lem4811235 _110796 _110799 x f s)). Qed.
Lemma lem4811238 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term243 _110796 _110799 f s x y) = (term243 _110796 _110799 f s x y).
Proof. exact (eq_refl (term243 _110796 _110799 f s x y)). Qed.
Lemma lem4811239 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term245 _110796 _110799 f s x y) = (term244 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811237 _110796 _110799 x f s) (@lem4811238 _110796 _110799 f s x y)). Qed.
Lemma lem4811240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811241 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term247 _110796 _110799 f s x y) = (term248 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811240) (@lem4811239 _110796 _110799 f s x y)). Qed.
Lemma lem4811242 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term101 _110796 _110799 x f s x') = (term91 _110796 _110799 x f x' s).
Proof. exact (eq_refl (term101 _110796 _110799 x f s x')). Qed.
Lemma lem4811243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811244 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term237 _110796 _110799 x f s x') = (term238 _110796 _110799 x f x' s).
Proof. exact (MK_COMB (@lem4811243) (@lem4811242 _110796 _110799 x f x' s)). Qed.
Lemma lem4811245 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term243 _110796 _110799 f s x y) = (term243 _110796 _110799 f s x y).
Proof. exact (eq_refl (term243 _110796 _110799 f s x y)). Qed.
Lemma lem4811246 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term249 _110796 _110799 x f s x' y) = (term250 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811244 _110796 _110799 x' f x s) (@lem4811245 _110796 _110799 f s x' y)). Qed.
Lemma lem4811247 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term251 _110796 _110799 f s x y) = (term252 _110796 _110799 f s x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811246 _110796 _110799 x' f s x y)). Qed.
Lemma lem4811248 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811249 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term246 _110796 _110799 f s x y) = (term253 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811248 _110799) (@lem4811247 _110796 _110799 f s x y)). Qed.
Lemma lem4811250 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : ((term245 _110796 _110799 f s x y) = (term246 _110796 _110799 f s x y)) = ((term244 _110796 _110799 f s x y) = (term253 _110796 _110799 f s x y)).
Proof. exact (MK_COMB (@lem4811241 _110796 _110799 f s x y) (@lem4811249 _110796 _110799 f s x y)). Qed.
Lemma lem4811251 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term244 _110796 _110799 f s x y) = (term253 _110796 _110799 f s x y).
Proof. exact (EQ_MP (@lem4811250 _110796 _110799 f s x y) (@lem4811231 _110796 _110799 f s x y)). Qed.
Lemma lem4811253 {A : Type'} (P : Prop) (Q : A -> Prop) : (term199 A P Q) = (term200 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4811254 {_110799 : Type'} (P : Prop) (Q : _110799 -> Prop) : (term199 _110799 P Q) = (term200 _110799 P Q).
Proof. exact (@lem4811253 _110799 P Q). Qed.
Lemma lem4811255 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term254 _110796 _110799 x f s x' y) = (term255 _110796 _110799 x f s x' y).
Proof. exact (@lem4811254 _110799 (term91 _110796 _110799 x' f x s) (term242 _110796 _110799 f s x' y)). Qed.
Lemma lem4811256 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term256 _110796 _110799 f s x' y x) = (term240 _110796 _110799 f x s x' y).
Proof. exact (eq_refl (term256 _110796 _110799 f s x' y x)). Qed.
Lemma lem4811257 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term257 _110796 _110799 f s x y) = (term242 _110796 _110799 f s x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811256 _110796 _110799 f x' s x y)). Qed.
Lemma lem4811258 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811259 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term258 _110796 _110799 f s x y) = (term243 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811258 _110799) (@lem4811257 _110796 _110799 f s x y)). Qed.
Lemma lem4811260 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term238 _110796 _110799 x f x' s) = (term238 _110796 _110799 x f x' s).
Proof. exact (eq_refl (term238 _110796 _110799 x f x' s)). Qed.
Lemma lem4811261 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term254 _110796 _110799 x f s x' y) = (term250 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811260 _110796 _110799 x' f x s) (@lem4811259 _110796 _110799 f s x' y)). Qed.
Lemma lem4811262 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811263 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term259 _110796 _110799 x f s x' y) = (term260 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811262) (@lem4811261 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811264 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term256 _110796 _110799 f s x y x') = (term240 _110796 _110799 f x' s x y).
Proof. exact (eq_refl (term256 _110796 _110799 f s x y x')). Qed.
Lemma lem4811265 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term238 _110796 _110799 x f x' s) = (term238 _110796 _110799 x f x' s).
Proof. exact (eq_refl (term238 _110796 _110799 x f x' s)). Qed.
Lemma lem4811266 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (x'' : _110796) (y : _110796) : (term261 _110796 _110799 x f s x'' y x') = (term262 _110796 _110799 x f x' s x'' y).
Proof. exact (MK_COMB (@lem4811265 _110796 _110799 x'' f x s) (@lem4811264 _110796 _110799 f x' s x'' y)). Qed.
Lemma lem4811267 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term263 _110796 _110799 x f s x' y) = (term264 _110796 _110799 x f s x' y).
Proof. exact (fun_ext (fun x'' : _110799 => @lem4811266 _110796 _110799 x f x'' s x' y)). Qed.
Lemma lem4811268 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811269 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term255 _110796 _110799 x f s x' y) = (term265 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811268 _110799) (@lem4811267 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811270 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : ((term254 _110796 _110799 x f s x' y) = (term255 _110796 _110799 x f s x' y)) = ((term250 _110796 _110799 x f s x' y) = (term265 _110796 _110799 x f s x' y)).
Proof. exact (MK_COMB (@lem4811263 _110796 _110799 x f s x' y) (@lem4811269 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811271 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term250 _110796 _110799 x f s x' y) = (term265 _110796 _110799 x f s x' y).
Proof. exact (EQ_MP (@lem4811270 _110796 _110799 x f s x' y) (@lem4811255 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811272 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term252 _110796 _110799 f s x y) = (term266 _110796 _110799 f s x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811271 _110796 _110799 x' f s x y)). Qed.
Lemma lem4811273 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811274 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term253 _110796 _110799 f s x y) = (term267 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811273 _110799) (@lem4811272 _110796 _110799 f s x y)). Qed.
Lemma lem4811275 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term244 _110796 _110799 f s x y) = (term267 _110796 _110799 f s x y).
Proof. exact (TRANS (@lem4811251 _110796 _110799 f s x y) (@lem4811274 _110796 _110799 f s x y)). Qed.
Lemma lem4811276 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term28 _110796 _110799 f s x y) = (term267 _110796 _110799 f s x y).
Proof. exact (TRANS (@lem4811227 _110796 _110799 f s x y) (@lem4811275 _110796 _110799 f s x y)). Qed.
Lemma lem4811277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811278 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term116 _110796 _110799 f s x y) = (term268 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811277) (@lem4811276 _110796 _110799 f s x y)). Qed.
Lemma lem4811279 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (term115 _110796 r x y) = (term115 _110796 r x y).
Proof. exact (eq_refl (term115 _110796 r x y)). Qed.
Lemma lem4811280 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term117 _110796 _110799 f s r x y) = (term269 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811278 _110796 _110799 f s x y) (@lem4811279 _110796 r x y)). Qed.
Lemma lem4811282 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4811283 {_110799 : Type'} (P : _110799 -> Prop) (Q : Prop) : (term228 _110799 P Q) = (term229 _110799 P Q).
Proof. exact (@lem4811282 _110799 P Q). Qed.
Lemma lem4811284 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term270 _110796 _110799 f s r x y) = (term271 _110796 _110799 f s r x y).
Proof. exact (@lem4811283 _110799 (term266 _110796 _110799 f s x y) (term115 _110796 r x y)). Qed.
Lemma lem4811285 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term272 _110796 _110799 f s x' y x) = (term265 _110796 _110799 x f s x' y).
Proof. exact (eq_refl (term272 _110796 _110799 f s x' y x)). Qed.
Lemma lem4811286 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term273 _110796 _110799 f s x y) = (term266 _110796 _110799 f s x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811285 _110796 _110799 x' f s x y)). Qed.
Lemma lem4811287 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811288 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term274 _110796 _110799 f s x y) = (term267 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811287 _110799) (@lem4811286 _110796 _110799 f s x y)). Qed.
Lemma lem4811289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811290 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term275 _110796 _110799 f s x y) = (term268 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811289) (@lem4811288 _110796 _110799 f s x y)). Qed.
Lemma lem4811291 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (term115 _110796 r x y) = (term115 _110796 r x y).
Proof. exact (eq_refl (term115 _110796 r x y)). Qed.
Lemma lem4811292 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term270 _110796 _110799 f s r x y) = (term269 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811290 _110796 _110799 f s x y) (@lem4811291 _110796 r x y)). Qed.
Lemma lem4811293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811294 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term276 _110796 _110799 f s r x y) = (term277 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811293) (@lem4811292 _110796 _110799 f s r x y)). Qed.
Lemma lem4811295 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term272 _110796 _110799 f s x' y x) = (term265 _110796 _110799 x f s x' y).
Proof. exact (eq_refl (term272 _110796 _110799 f s x' y x)). Qed.
Lemma lem4811296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811297 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term278 _110796 _110799 f s x' y x) = (term279 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811296) (@lem4811295 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811298 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (term115 _110796 r x y) = (term115 _110796 r x y).
Proof. exact (eq_refl (term115 _110796 r x y)). Qed.
Lemma lem4811299 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term280 _110796 _110799 f s x r x' y) = (term281 _110796 _110799 x f s r x' y).
Proof. exact (MK_COMB (@lem4811297 _110796 _110799 x f s x' y) (@lem4811298 _110796 r x' y)). Qed.
Lemma lem4811300 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term282 _110796 _110799 f s r x y) = (term283 _110796 _110799 f s r x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811299 _110796 _110799 x' f s r x y)). Qed.
Lemma lem4811301 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811302 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term271 _110796 _110799 f s r x y) = (term284 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811301 _110799) (@lem4811300 _110796 _110799 f s r x y)). Qed.
Lemma lem4811303 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : ((term270 _110796 _110799 f s r x y) = (term271 _110796 _110799 f s r x y)) = ((term269 _110796 _110799 f s r x y) = (term284 _110796 _110799 f s r x y)).
Proof. exact (MK_COMB (@lem4811294 _110796 _110799 f s r x y) (@lem4811302 _110796 _110799 f s r x y)). Qed.
Lemma lem4811304 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term269 _110796 _110799 f s r x y) = (term284 _110796 _110799 f s r x y).
Proof. exact (EQ_MP (@lem4811303 _110796 _110799 f s r x y) (@lem4811284 _110796 _110799 f s r x y)). Qed.
Lemma lem4811306 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4811307 {_110799 : Type'} (P : _110799 -> Prop) (Q : Prop) : (term228 _110799 P Q) = (term229 _110799 P Q).
Proof. exact (@lem4811306 _110799 P Q). Qed.
Lemma lem4811308 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term285 _110796 _110799 x f s r x' y) = (term286 _110796 _110799 x f s r x' y).
Proof. exact (@lem4811307 _110799 (term264 _110796 _110799 x f s x' y) (term115 _110796 r x' y)). Qed.
Lemma lem4811309 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (x'' : _110796) (y : _110796) : (term287 _110796 _110799 x f s x'' y x') = (term262 _110796 _110799 x f x' s x'' y).
Proof. exact (eq_refl (term287 _110796 _110799 x f s x'' y x')). Qed.
Lemma lem4811310 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term288 _110796 _110799 x f s x' y) = (term264 _110796 _110799 x f s x' y).
Proof. exact (fun_ext (fun x'' : _110799 => @lem4811309 _110796 _110799 x f x'' s x' y)). Qed.
Lemma lem4811311 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811312 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term289 _110796 _110799 x f s x' y) = (term265 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811311 _110799) (@lem4811310 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811314 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term290 _110796 _110799 x f s x' y) = (term279 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811313) (@lem4811312 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811315 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (term115 _110796 r x y) = (term115 _110796 r x y).
Proof. exact (eq_refl (term115 _110796 r x y)). Qed.
Lemma lem4811316 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term285 _110796 _110799 x f s r x' y) = (term281 _110796 _110799 x f s r x' y).
Proof. exact (MK_COMB (@lem4811314 _110796 _110799 x f s x' y) (@lem4811315 _110796 r x' y)). Qed.
Lemma lem4811317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811318 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term291 _110796 _110799 x f s r x' y) = (term292 _110796 _110799 x f s r x' y).
Proof. exact (MK_COMB (@lem4811317) (@lem4811316 _110796 _110799 x f s r x' y)). Qed.
Lemma lem4811319 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (x'' : _110796) (y : _110796) : (term287 _110796 _110799 x f s x'' y x') = (term262 _110796 _110799 x f x' s x'' y).
Proof. exact (eq_refl (term287 _110796 _110799 x f s x'' y x')). Qed.
Lemma lem4811320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811321 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (x'' : _110796) (y : _110796) : (term293 _110796 _110799 x f s x'' y x') = (term294 _110796 _110799 x f x' s x'' y).
Proof. exact (MK_COMB (@lem4811320) (@lem4811319 _110796 _110799 x f x' s x'' y)). Qed.
Lemma lem4811322 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (term115 _110796 r x y) = (term115 _110796 r x y).
Proof. exact (eq_refl (term115 _110796 r x y)). Qed.
Lemma lem4811323 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (x'' : _110796) (y : _110796) : (term295 _110796 _110799 x f s x' r x'' y) = (term296 _110796 _110799 x f x' s r x'' y).
Proof. exact (MK_COMB (@lem4811321 _110796 _110799 x f x' s x'' y) (@lem4811322 _110796 r x'' y)). Qed.
Lemma lem4811324 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term297 _110796 _110799 x f s r x' y) = (term298 _110796 _110799 x f s r x' y).
Proof. exact (fun_ext (fun x'' : _110799 => @lem4811323 _110796 _110799 x f x'' s r x' y)). Qed.
Lemma lem4811325 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811326 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term286 _110796 _110799 x f s r x' y) = (term299 _110796 _110799 x f s r x' y).
Proof. exact (MK_COMB (@lem4811325 _110799) (@lem4811324 _110796 _110799 x f s r x' y)). Qed.
Lemma lem4811327 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : ((term285 _110796 _110799 x f s r x' y) = (term286 _110796 _110799 x f s r x' y)) = ((term281 _110796 _110799 x f s r x' y) = (term299 _110796 _110799 x f s r x' y)).
Proof. exact (MK_COMB (@lem4811318 _110796 _110799 x f s r x' y) (@lem4811326 _110796 _110799 x f s r x' y)). Qed.
Lemma lem4811328 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term281 _110796 _110799 x f s r x' y) = (term299 _110796 _110799 x f s r x' y).
Proof. exact (EQ_MP (@lem4811327 _110796 _110799 x f s r x' y) (@lem4811308 _110796 _110799 x f s r x' y)). Qed.
Lemma lem4811329 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term283 _110796 _110799 f s r x y) = (term300 _110796 _110799 f s r x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811328 _110796 _110799 x' f s r x y)). Qed.
Lemma lem4811330 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811331 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term284 _110796 _110799 f s r x y) = (term301 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811330 _110799) (@lem4811329 _110796 _110799 f s r x y)). Qed.
Lemma lem4811332 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term269 _110796 _110799 f s r x y) = (term301 _110796 _110799 f s r x y).
Proof. exact (TRANS (@lem4811304 _110796 _110799 f s r x y) (@lem4811331 _110796 _110799 f s r x y)). Qed.
Lemma lem4811333 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term117 _110796 _110799 f s r x y) = (term301 _110796 _110799 f s r x y).
Proof. exact (TRANS (@lem4811280 _110796 _110799 f s r x y) (@lem4811332 _110796 _110799 f s r x y)). Qed.
Lemma lem4811334 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term130 _110796 _110799 f s r x) = (term302 _110796 _110799 f s r x).
Proof. exact (fun_ext (fun y : _110796 => @lem4811333 _110796 _110799 f s r x y)). Qed.
Lemma lem4811335 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811336 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term131 _110796 _110799 f s r x) = (term303 _110796 _110799 f s r x).
Proof. exact (MK_COMB (@lem4811335 _110796) (@lem4811334 _110796 _110799 f s r x)). Qed.
Lemma lem4811337 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term139 _110796 _110799 f s r) = (term304 _110796 _110799 f s r).
Proof. exact (fun_ext (fun x : _110796 => @lem4811336 _110796 _110799 f s r x)). Qed.
Lemma lem4811338 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811339 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term140 _110796 _110799 f s r) = (term305 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4811338 _110796) (@lem4811337 _110796 _110799 f s r)). Qed.
Lemma lem4811340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811341 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term188 _110796 _110799 f s r) = (term306 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4811340) (@lem4811339 _110796 _110799 f s r)). Qed.
Lemma lem4811342 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term186 _110796 _110799 s r f) = (term186 _110796 _110799 s r f).
Proof. exact (eq_refl (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811343 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term190 _110796 _110799 s r f) = (term307 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811341 _110796 _110799 f s r) (@lem4811342 _110796 _110799 s r f)). Qed.
Lemma lem4811345 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4811346 {_110796 : Type'} (P : _110796 -> Prop) (Q : Prop) : (term228 _110796 P Q) = (term229 _110796 P Q).
Proof. exact (@lem4811345 _110796 P Q). Qed.
Lemma lem4811347 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term308 _110796 _110799 s r f) = (term309 _110796 _110799 s r f).
Proof. exact (@lem4811346 _110796 (term304 _110796 _110799 f s r) (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811348 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term310 _110796 _110799 f s r x) = (term303 _110796 _110799 f s r x).
Proof. exact (eq_refl (term310 _110796 _110799 f s r x)). Qed.
Lemma lem4811349 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term311 _110796 _110799 f s r) = (term304 _110796 _110799 f s r).
Proof. exact (fun_ext (fun x : _110796 => @lem4811348 _110796 _110799 f s r x)). Qed.
Lemma lem4811350 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811351 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term312 _110796 _110799 f s r) = (term305 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4811350 _110796) (@lem4811349 _110796 _110799 f s r)). Qed.
Lemma lem4811352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811353 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term313 _110796 _110799 f s r) = (term306 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4811352) (@lem4811351 _110796 _110799 f s r)). Qed.
Lemma lem4811354 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term186 _110796 _110799 s r f) = (term186 _110796 _110799 s r f).
Proof. exact (eq_refl (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811355 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term308 _110796 _110799 s r f) = (term307 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811353 _110796 _110799 f s r) (@lem4811354 _110796 _110799 s r f)). Qed.
Lemma lem4811356 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811357 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term314 _110796 _110799 s r f) = (term315 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811356) (@lem4811355 _110796 _110799 s r f)). Qed.
Lemma lem4811358 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term310 _110796 _110799 f s r x) = (term303 _110796 _110799 f s r x).
Proof. exact (eq_refl (term310 _110796 _110799 f s r x)). Qed.
Lemma lem4811359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811360 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term316 _110796 _110799 f s r x) = (term317 _110796 _110799 f s r x).
Proof. exact (MK_COMB (@lem4811359) (@lem4811358 _110796 _110799 f s r x)). Qed.
Lemma lem4811361 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term186 _110796 _110799 s r f) = (term186 _110796 _110799 s r f).
Proof. exact (eq_refl (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811362 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term318 _110796 _110799 x s r f) = (term319 _110796 _110799 x s r f).
Proof. exact (MK_COMB (@lem4811360 _110796 _110799 f s r x) (@lem4811361 _110796 _110799 s r f)). Qed.
Lemma lem4811363 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term320 _110796 _110799 s r f) = (term321 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110796 => @lem4811362 _110796 _110799 x s r f)). Qed.
Lemma lem4811364 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811365 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term309 _110796 _110799 s r f) = (term322 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811364 _110796) (@lem4811363 _110796 _110799 s r f)). Qed.
Lemma lem4811366 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term308 _110796 _110799 s r f) = (term309 _110796 _110799 s r f)) = ((term307 _110796 _110799 s r f) = (term322 _110796 _110799 s r f)).
Proof. exact (MK_COMB (@lem4811357 _110796 _110799 s r f) (@lem4811365 _110796 _110799 s r f)). Qed.
Lemma lem4811367 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term307 _110796 _110799 s r f) = (term322 _110796 _110799 s r f).
Proof. exact (EQ_MP (@lem4811366 _110796 _110799 s r f) (@lem4811347 _110796 _110799 s r f)). Qed.
Lemma lem4811369 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4811370 {_110796 : Type'} (P : _110796 -> Prop) (Q : Prop) : (term228 _110796 P Q) = (term229 _110796 P Q).
Proof. exact (@lem4811369 _110796 P Q). Qed.
Lemma lem4811371 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term323 _110796 _110799 x s r f) = (term324 _110796 _110799 x s r f).
Proof. exact (@lem4811370 _110796 (term302 _110796 _110799 f s r x) (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811372 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term325 _110796 _110799 f s r x y) = (term301 _110796 _110799 f s r x y).
Proof. exact (eq_refl (term325 _110796 _110799 f s r x y)). Qed.
Lemma lem4811373 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term326 _110796 _110799 f s r x) = (term302 _110796 _110799 f s r x).
Proof. exact (fun_ext (fun y : _110796 => @lem4811372 _110796 _110799 f s r x y)). Qed.
Lemma lem4811374 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811375 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term327 _110796 _110799 f s r x) = (term303 _110796 _110799 f s r x).
Proof. exact (MK_COMB (@lem4811374 _110796) (@lem4811373 _110796 _110799 f s r x)). Qed.
Lemma lem4811376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811377 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term328 _110796 _110799 f s r x) = (term317 _110796 _110799 f s r x).
Proof. exact (MK_COMB (@lem4811376) (@lem4811375 _110796 _110799 f s r x)). Qed.
Lemma lem4811378 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term186 _110796 _110799 s r f) = (term186 _110796 _110799 s r f).
Proof. exact (eq_refl (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811379 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term323 _110796 _110799 x s r f) = (term319 _110796 _110799 x s r f).
Proof. exact (MK_COMB (@lem4811377 _110796 _110799 f s r x) (@lem4811378 _110796 _110799 s r f)). Qed.
Lemma lem4811380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811381 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term329 _110796 _110799 x s r f) = (term330 _110796 _110799 x s r f).
Proof. exact (MK_COMB (@lem4811380) (@lem4811379 _110796 _110799 x s r f)). Qed.
Lemma lem4811382 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term325 _110796 _110799 f s r x y) = (term301 _110796 _110799 f s r x y).
Proof. exact (eq_refl (term325 _110796 _110799 f s r x y)). Qed.
Lemma lem4811383 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811384 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term331 _110796 _110799 f s r x y) = (term332 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811383) (@lem4811382 _110796 _110799 f s r x y)). Qed.
Lemma lem4811385 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term186 _110796 _110799 s r f) = (term186 _110796 _110799 s r f).
Proof. exact (eq_refl (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811386 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term333 _110796 _110799 x y s r f) = (term334 _110796 _110799 x y s r f).
Proof. exact (MK_COMB (@lem4811384 _110796 _110799 f s r x y) (@lem4811385 _110796 _110799 s r f)). Qed.
Lemma lem4811387 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term335 _110796 _110799 x s r f) = (term336 _110796 _110799 x s r f).
Proof. exact (fun_ext (fun y : _110796 => @lem4811386 _110796 _110799 x y s r f)). Qed.
Lemma lem4811388 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811389 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term324 _110796 _110799 x s r f) = (term337 _110796 _110799 x s r f).
Proof. exact (MK_COMB (@lem4811388 _110796) (@lem4811387 _110796 _110799 x s r f)). Qed.
Lemma lem4811390 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term323 _110796 _110799 x s r f) = (term324 _110796 _110799 x s r f)) = ((term319 _110796 _110799 x s r f) = (term337 _110796 _110799 x s r f)).
Proof. exact (MK_COMB (@lem4811381 _110796 _110799 x s r f) (@lem4811389 _110796 _110799 x s r f)). Qed.
Lemma lem4811391 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term319 _110796 _110799 x s r f) = (term337 _110796 _110799 x s r f).
Proof. exact (EQ_MP (@lem4811390 _110796 _110799 x s r f) (@lem4811371 _110796 _110799 x s r f)). Qed.
Lemma lem4811393 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4811394 {_110799 : Type'} (P : _110799 -> Prop) (Q : Prop) : (term228 _110799 P Q) = (term229 _110799 P Q).
Proof. exact (@lem4811393 _110799 P Q). Qed.
Lemma lem4811395 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term338 _110796 _110799 x y s r f) = (term339 _110796 _110799 x y s r f).
Proof. exact (@lem4811394 _110799 (term300 _110796 _110799 f s r x y) (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811396 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term340 _110796 _110799 f s r x' y x) = (term299 _110796 _110799 x f s r x' y).
Proof. exact (eq_refl (term340 _110796 _110799 f s r x' y x)). Qed.
Lemma lem4811397 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term341 _110796 _110799 f s r x y) = (term300 _110796 _110799 f s r x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811396 _110796 _110799 x' f s r x y)). Qed.
Lemma lem4811398 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811399 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term342 _110796 _110799 f s r x y) = (term301 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811398 _110799) (@lem4811397 _110796 _110799 f s r x y)). Qed.
Lemma lem4811400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811401 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term343 _110796 _110799 f s r x y) = (term332 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811400) (@lem4811399 _110796 _110799 f s r x y)). Qed.
Lemma lem4811402 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term186 _110796 _110799 s r f) = (term186 _110796 _110799 s r f).
Proof. exact (eq_refl (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811403 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term338 _110796 _110799 x y s r f) = (term334 _110796 _110799 x y s r f).
Proof. exact (MK_COMB (@lem4811401 _110796 _110799 f s r x y) (@lem4811402 _110796 _110799 s r f)). Qed.
Lemma lem4811404 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811405 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term344 _110796 _110799 x y s r f) = (term345 _110796 _110799 x y s r f).
Proof. exact (MK_COMB (@lem4811404) (@lem4811403 _110796 _110799 x y s r f)). Qed.
Lemma lem4811406 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term340 _110796 _110799 f s r x' y x) = (term299 _110796 _110799 x f s r x' y).
Proof. exact (eq_refl (term340 _110796 _110799 f s r x' y x)). Qed.
Lemma lem4811407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811408 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term346 _110796 _110799 f s r x' y x) = (term347 _110796 _110799 x f s r x' y).
Proof. exact (MK_COMB (@lem4811407) (@lem4811406 _110796 _110799 x f s r x' y)). Qed.
Lemma lem4811409 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term186 _110796 _110799 s r f) = (term186 _110796 _110799 s r f).
Proof. exact (eq_refl (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811410 {_110796 _110799 : Type'} (x : _110799) (x' : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term348 _110796 _110799 x' y x s r f) = (term349 _110796 _110799 x x' y s r f).
Proof. exact (MK_COMB (@lem4811408 _110796 _110799 x f s r x' y) (@lem4811409 _110796 _110799 s r f)). Qed.
Lemma lem4811411 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term350 _110796 _110799 x y s r f) = (term351 _110796 _110799 x y s r f).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811410 _110796 _110799 x' x y s r f)). Qed.
Lemma lem4811412 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811413 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term339 _110796 _110799 x y s r f) = (term352 _110796 _110799 x y s r f).
Proof. exact (MK_COMB (@lem4811412 _110799) (@lem4811411 _110796 _110799 x y s r f)). Qed.
Lemma lem4811414 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term338 _110796 _110799 x y s r f) = (term339 _110796 _110799 x y s r f)) = ((term334 _110796 _110799 x y s r f) = (term352 _110796 _110799 x y s r f)).
Proof. exact (MK_COMB (@lem4811405 _110796 _110799 x y s r f) (@lem4811413 _110796 _110799 x y s r f)). Qed.
Lemma lem4811415 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term334 _110796 _110799 x y s r f) = (term352 _110796 _110799 x y s r f).
Proof. exact (EQ_MP (@lem4811414 _110796 _110799 x y s r f) (@lem4811395 _110796 _110799 x y s r f)). Qed.
Lemma lem4811417 {A : Type'} (P : A -> Prop) (Q : Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4811418 {_110799 : Type'} (P : _110799 -> Prop) (Q : Prop) : (term228 _110799 P Q) = (term229 _110799 P Q).
Proof. exact (@lem4811417 _110799 P Q). Qed.
Lemma lem4811419 {_110796 _110799 : Type'} (x : _110799) (x' : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term353 _110796 _110799 x x' y s r f) = (term354 _110796 _110799 x x' y s r f).
Proof. exact (@lem4811418 _110799 (term298 _110796 _110799 x f s r x' y) (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811420 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (x'' : _110796) (y : _110796) : (term355 _110796 _110799 x f s r x'' y x') = (term296 _110796 _110799 x f x' s r x'' y).
Proof. exact (eq_refl (term355 _110796 _110799 x f s r x'' y x')). Qed.
Lemma lem4811421 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term356 _110796 _110799 x f s r x' y) = (term298 _110796 _110799 x f s r x' y).
Proof. exact (fun_ext (fun x'' : _110799 => @lem4811420 _110796 _110799 x f x'' s r x' y)). Qed.
Lemma lem4811422 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811423 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term357 _110796 _110799 x f s r x' y) = (term299 _110796 _110799 x f s r x' y).
Proof. exact (MK_COMB (@lem4811422 _110799) (@lem4811421 _110796 _110799 x f s r x' y)). Qed.
Lemma lem4811424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811425 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term358 _110796 _110799 x f s r x' y) = (term347 _110796 _110799 x f s r x' y).
Proof. exact (MK_COMB (@lem4811424) (@lem4811423 _110796 _110799 x f s r x' y)). Qed.
Lemma lem4811426 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term186 _110796 _110799 s r f) = (term186 _110796 _110799 s r f).
Proof. exact (eq_refl (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811427 {_110796 _110799 : Type'} (x : _110799) (x' : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term353 _110796 _110799 x x' y s r f) = (term349 _110796 _110799 x x' y s r f).
Proof. exact (MK_COMB (@lem4811425 _110796 _110799 x f s r x' y) (@lem4811426 _110796 _110799 s r f)). Qed.
Lemma lem4811428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811429 {_110796 _110799 : Type'} (x : _110799) (x' : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term359 _110796 _110799 x x' y s r f) = (term360 _110796 _110799 x x' y s r f).
Proof. exact (MK_COMB (@lem4811428) (@lem4811427 _110796 _110799 x x' y s r f)). Qed.
Lemma lem4811430 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (x'' : _110796) (y : _110796) : (term355 _110796 _110799 x f s r x'' y x') = (term296 _110796 _110799 x f x' s r x'' y).
Proof. exact (eq_refl (term355 _110796 _110799 x f s r x'' y x')). Qed.
Lemma lem4811431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811432 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (x'' : _110796) (y : _110796) : (term361 _110796 _110799 x f s r x'' y x') = (term362 _110796 _110799 x f x' s r x'' y).
Proof. exact (MK_COMB (@lem4811431) (@lem4811430 _110796 _110799 x f x' s r x'' y)). Qed.
Lemma lem4811433 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term186 _110796 _110799 s r f) = (term186 _110796 _110799 s r f).
Proof. exact (eq_refl (term186 _110796 _110799 s r f)). Qed.
Lemma lem4811434 {_110796 _110799 : Type'} (x : _110799) (x' : _110799) (x'' : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term363 _110796 _110799 x x'' y x' s r f) = (term364 _110796 _110799 x x' x'' y s r f).
Proof. exact (MK_COMB (@lem4811432 _110796 _110799 x f x' s r x'' y) (@lem4811433 _110796 _110799 s r f)). Qed.
Lemma lem4811435 {_110796 _110799 : Type'} (x : _110799) (x' : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term365 _110796 _110799 x x' y s r f) = (term366 _110796 _110799 x x' y s r f).
Proof. exact (fun_ext (fun x'' : _110799 => @lem4811434 _110796 _110799 x x'' x' y s r f)). Qed.
Lemma lem4811436 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811437 {_110796 _110799 : Type'} (x : _110799) (x' : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term354 _110796 _110799 x x' y s r f) = (term367 _110796 _110799 x x' y s r f).
Proof. exact (MK_COMB (@lem4811436 _110799) (@lem4811435 _110796 _110799 x x' y s r f)). Qed.
Lemma lem4811438 {_110796 _110799 : Type'} (x : _110799) (x' : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term353 _110796 _110799 x x' y s r f) = (term354 _110796 _110799 x x' y s r f)) = ((term349 _110796 _110799 x x' y s r f) = (term367 _110796 _110799 x x' y s r f)).
Proof. exact (MK_COMB (@lem4811429 _110796 _110799 x x' y s r f) (@lem4811437 _110796 _110799 x x' y s r f)). Qed.
Lemma lem4811439 {_110796 _110799 : Type'} (x : _110799) (x' : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term349 _110796 _110799 x x' y s r f) = (term367 _110796 _110799 x x' y s r f).
Proof. exact (EQ_MP (@lem4811438 _110796 _110799 x x' y s r f) (@lem4811419 _110796 _110799 x x' y s r f)). Qed.
Lemma lem4811440 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term351 _110796 _110799 x y s r f) = (term368 _110796 _110799 x y s r f).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811439 _110796 _110799 x' x y s r f)). Qed.
Lemma lem4811441 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811442 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term352 _110796 _110799 x y s r f) = (term369 _110796 _110799 x y s r f).
Proof. exact (MK_COMB (@lem4811441 _110799) (@lem4811440 _110796 _110799 x y s r f)). Qed.
Lemma lem4811443 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term334 _110796 _110799 x y s r f) = (term369 _110796 _110799 x y s r f).
Proof. exact (TRANS (@lem4811415 _110796 _110799 x y s r f) (@lem4811442 _110796 _110799 x y s r f)). Qed.
Lemma lem4811444 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term336 _110796 _110799 x s r f) = (term370 _110796 _110799 x s r f).
Proof. exact (fun_ext (fun y : _110796 => @lem4811443 _110796 _110799 x y s r f)). Qed.
Lemma lem4811445 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811446 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term337 _110796 _110799 x s r f) = (term371 _110796 _110799 x s r f).
Proof. exact (MK_COMB (@lem4811445 _110796) (@lem4811444 _110796 _110799 x s r f)). Qed.
Lemma lem4811447 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term319 _110796 _110799 x s r f) = (term371 _110796 _110799 x s r f).
Proof. exact (TRANS (@lem4811391 _110796 _110799 x s r f) (@lem4811446 _110796 _110799 x s r f)). Qed.
Lemma lem4811448 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term321 _110796 _110799 s r f) = (term372 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110796 => @lem4811447 _110796 _110799 x s r f)). Qed.
Lemma lem4811449 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811450 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term322 _110796 _110799 s r f) = (term373 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811449 _110796) (@lem4811448 _110796 _110799 s r f)). Qed.
Lemma lem4811451 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term307 _110796 _110799 s r f) = (term373 _110796 _110799 s r f).
Proof. exact (TRANS (@lem4811367 _110796 _110799 s r f) (@lem4811450 _110796 _110799 s r f)). Qed.
Lemma lem4811452 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term190 _110796 _110799 s r f) = (term373 _110796 _110799 s r f).
Proof. exact (TRANS (@lem4811343 _110796 _110799 s r f) (@lem4811451 _110796 _110799 s r f)). Qed.
Lemma lem4811453 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term198 _110796 _110799 s r f) = (term374 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811201 _110796 _110799 s r f) (@lem4811452 _110796 _110799 s r f)). Qed.
Lemma lem4811457 {A : Type'} (P : A -> Prop) (Q : Prop) : (term375 A P Q) = (term376 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4811458 {_110799 : Type'} (P : _110799 -> Prop) (Q : Prop) : (term375 _110799 P Q) = (term376 _110799 P Q).
Proof. exact (@lem4811457 _110799 P Q). Qed.
Lemma lem4811459 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term377 _110796 _110799 s r f) = (term378 _110796 _110799 s r f).
Proof. exact (@lem4811458 _110799 (term225 _110796 _110799 s r f) (term373 _110796 _110799 s r f)). Qed.
Lemma lem4811460 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term379 _110796 _110799 s r f x) = (term224 _110796 _110799 s r x f).
Proof. exact (eq_refl (term379 _110796 _110799 s r f x)). Qed.
Lemma lem4811461 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term380 _110796 _110799 s r f) = (term225 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4811460 _110796 _110799 s r x f)). Qed.
Lemma lem4811462 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811463 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term381 _110796 _110799 s r f) = (term226 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811462 _110799) (@lem4811461 _110796 _110799 s r f)). Qed.
Lemma lem4811464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811465 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term382 _110796 _110799 s r f) = (term227 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811464) (@lem4811463 _110796 _110799 s r f)). Qed.
Lemma lem4811466 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term373 _110796 _110799 s r f) = (term373 _110796 _110799 s r f).
Proof. exact (eq_refl (term373 _110796 _110799 s r f)). Qed.
Lemma lem4811467 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term377 _110796 _110799 s r f) = (term374 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811465 _110796 _110799 s r f) (@lem4811466 _110796 _110799 s r f)). Qed.
Lemma lem4811468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811469 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term383 _110796 _110799 s r f) = (term384 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811468) (@lem4811467 _110796 _110799 s r f)). Qed.
Lemma lem4811470 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term379 _110796 _110799 s r f x) = (term224 _110796 _110799 s r x f).
Proof. exact (eq_refl (term379 _110796 _110799 s r f x)). Qed.
Lemma lem4811471 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811472 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term385 _110796 _110799 s r f x) = (term386 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4811471) (@lem4811470 _110796 _110799 s r x f)). Qed.
Lemma lem4811473 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term373 _110796 _110799 s r f) = (term373 _110796 _110799 s r f).
Proof. exact (eq_refl (term373 _110796 _110799 s r f)). Qed.
Lemma lem4811474 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term387 _110796 _110799 x s r f) = (term388 _110796 _110799 x s r f).
Proof. exact (MK_COMB (@lem4811472 _110796 _110799 s r x f) (@lem4811473 _110796 _110799 s r f)). Qed.
Lemma lem4811475 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term389 _110796 _110799 s r f) = (term390 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4811474 _110796 _110799 x s r f)). Qed.
Lemma lem4811476 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811477 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term378 _110796 _110799 s r f) = (term391 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811476 _110799) (@lem4811475 _110796 _110799 s r f)). Qed.
Lemma lem4811478 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term377 _110796 _110799 s r f) = (term378 _110796 _110799 s r f)) = ((term374 _110796 _110799 s r f) = (term391 _110796 _110799 s r f)).
Proof. exact (MK_COMB (@lem4811469 _110796 _110799 s r f) (@lem4811477 _110796 _110799 s r f)). Qed.
Lemma lem4811479 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term374 _110796 _110799 s r f) = (term391 _110796 _110799 s r f).
Proof. exact (EQ_MP (@lem4811478 _110796 _110799 s r f) (@lem4811459 _110796 _110799 s r f)). Qed.
Lemma lem4811483 {A : Type'} (P : A -> Prop) (Q : Prop) : (term375 A P Q) = (term376 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4811484 {_110799 : Type'} (P : _110799 -> Prop) (Q : Prop) : (term375 _110799 P Q) = (term376 _110799 P Q).
Proof. exact (@lem4811483 _110799 P Q). Qed.
Lemma lem4811485 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term392 _110796 _110799 x s r f) = (term393 _110796 _110799 x s r f).
Proof. exact (@lem4811484 _110799 (term223 _110796 _110799 s r x f) (term373 _110796 _110799 s r f)). Qed.
Lemma lem4811486 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term394 _110796 _110799 s r x f y) = (term221 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term394 _110796 _110799 s r x f y)). Qed.
Lemma lem4811487 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term395 _110796 _110799 s r x f) = (term223 _110796 _110799 s r x f).
Proof. exact (fun_ext (fun y : _110799 => @lem4811486 _110796 _110799 s r x f y)). Qed.
Lemma lem4811488 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811489 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term396 _110796 _110799 s r x f) = (term224 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4811488 _110799) (@lem4811487 _110796 _110799 s r x f)). Qed.
Lemma lem4811490 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811491 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term397 _110796 _110799 s r x f) = (term386 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4811490) (@lem4811489 _110796 _110799 s r x f)). Qed.
Lemma lem4811492 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term373 _110796 _110799 s r f) = (term373 _110796 _110799 s r f).
Proof. exact (eq_refl (term373 _110796 _110799 s r f)). Qed.
Lemma lem4811493 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term392 _110796 _110799 x s r f) = (term388 _110796 _110799 x s r f).
Proof. exact (MK_COMB (@lem4811491 _110796 _110799 s r x f) (@lem4811492 _110796 _110799 s r f)). Qed.
Lemma lem4811494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811495 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term398 _110796 _110799 x s r f) = (term399 _110796 _110799 x s r f).
Proof. exact (MK_COMB (@lem4811494) (@lem4811493 _110796 _110799 x s r f)). Qed.
Lemma lem4811496 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term394 _110796 _110799 s r x f y) = (term221 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term394 _110796 _110799 s r x f y)). Qed.
Lemma lem4811497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811498 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term400 _110796 _110799 s r x f y) = (term401 _110796 _110799 s r x f y).
Proof. exact (MK_COMB (@lem4811497) (@lem4811496 _110796 _110799 s r x f y)). Qed.
Lemma lem4811499 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term373 _110796 _110799 s r f) = (term373 _110796 _110799 s r f).
Proof. exact (eq_refl (term373 _110796 _110799 s r f)). Qed.
Lemma lem4811500 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term402 _110796 _110799 x y s r f) = (term403 _110796 _110799 x y s r f).
Proof. exact (MK_COMB (@lem4811498 _110796 _110799 s r x f y) (@lem4811499 _110796 _110799 s r f)). Qed.
Lemma lem4811501 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term404 _110796 _110799 x s r f) = (term405 _110796 _110799 x s r f).
Proof. exact (fun_ext (fun y : _110799 => @lem4811500 _110796 _110799 x y s r f)). Qed.
Lemma lem4811502 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811503 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term393 _110796 _110799 x s r f) = (term406 _110796 _110799 x s r f).
Proof. exact (MK_COMB (@lem4811502 _110799) (@lem4811501 _110796 _110799 x s r f)). Qed.
Lemma lem4811504 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term392 _110796 _110799 x s r f) = (term393 _110796 _110799 x s r f)) = ((term388 _110796 _110799 x s r f) = (term406 _110796 _110799 x s r f)).
Proof. exact (MK_COMB (@lem4811495 _110796 _110799 x s r f) (@lem4811503 _110796 _110799 x s r f)). Qed.
Lemma lem4811505 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term388 _110796 _110799 x s r f) = (term406 _110796 _110799 x s r f).
Proof. exact (EQ_MP (@lem4811504 _110796 _110799 x s r f) (@lem4811485 _110796 _110799 x s r f)). Qed.
Lemma lem4811507 {A : Type'} (P : Prop) (Q : A -> Prop) : (term407 A P Q) = (term408 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4811508 {_110796 : Type'} (P : Prop) (Q : _110796 -> Prop) : (term407 _110796 P Q) = (term408 _110796 P Q).
Proof. exact (@lem4811507 _110796 P Q). Qed.
Lemma lem4811509 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term409 _110796 _110799 x y s r f) = (term410 _110796 _110799 x y s r f).
Proof. exact (@lem4811508 _110796 (term221 _110796 _110799 s r x f y) (term372 _110796 _110799 s r f)). Qed.
Lemma lem4811510 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term411 _110796 _110799 s r f x) = (term371 _110796 _110799 x s r f).
Proof. exact (eq_refl (term411 _110796 _110799 s r f x)). Qed.
Lemma lem4811511 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term412 _110796 _110799 s r f) = (term372 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110796 => @lem4811510 _110796 _110799 x s r f)). Qed.
Lemma lem4811512 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811513 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term413 _110796 _110799 s r f) = (term373 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811512 _110796) (@lem4811511 _110796 _110799 s r f)). Qed.
Lemma lem4811514 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term401 _110796 _110799 s r x f y) = (term401 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term401 _110796 _110799 s r x f y)). Qed.
Lemma lem4811515 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term409 _110796 _110799 x y s r f) = (term403 _110796 _110799 x y s r f).
Proof. exact (MK_COMB (@lem4811514 _110796 _110799 s r x f y) (@lem4811513 _110796 _110799 s r f)). Qed.
Lemma lem4811516 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811517 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term414 _110796 _110799 x y s r f) = (term415 _110796 _110799 x y s r f).
Proof. exact (MK_COMB (@lem4811516) (@lem4811515 _110796 _110799 x y s r f)). Qed.
Lemma lem4811518 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term411 _110796 _110799 s r f x) = (term371 _110796 _110799 x s r f).
Proof. exact (eq_refl (term411 _110796 _110799 s r f x)). Qed.
Lemma lem4811519 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term401 _110796 _110799 s r x f y) = (term401 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term401 _110796 _110799 s r x f y)). Qed.
Lemma lem4811520 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term416 _110796 _110799 x y s r f x') = (term417 _110796 _110799 x y x' s r f).
Proof. exact (MK_COMB (@lem4811519 _110796 _110799 s r x f y) (@lem4811518 _110796 _110799 x' s r f)). Qed.
Lemma lem4811521 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term418 _110796 _110799 x y s r f) = (term419 _110796 _110799 x y s r f).
Proof. exact (fun_ext (fun x' : _110796 => @lem4811520 _110796 _110799 x y x' s r f)). Qed.
Lemma lem4811522 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811523 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term410 _110796 _110799 x y s r f) = (term420 _110796 _110799 x y s r f).
Proof. exact (MK_COMB (@lem4811522 _110796) (@lem4811521 _110796 _110799 x y s r f)). Qed.
Lemma lem4811524 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term409 _110796 _110799 x y s r f) = (term410 _110796 _110799 x y s r f)) = ((term403 _110796 _110799 x y s r f) = (term420 _110796 _110799 x y s r f)).
Proof. exact (MK_COMB (@lem4811517 _110796 _110799 x y s r f) (@lem4811523 _110796 _110799 x y s r f)). Qed.
Lemma lem4811525 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term403 _110796 _110799 x y s r f) = (term420 _110796 _110799 x y s r f).
Proof. exact (EQ_MP (@lem4811524 _110796 _110799 x y s r f) (@lem4811509 _110796 _110799 x y s r f)). Qed.
Lemma lem4811527 {A : Type'} (P : Prop) (Q : A -> Prop) : (term407 A P Q) = (term408 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4811528 {_110796 : Type'} (P : Prop) (Q : _110796 -> Prop) : (term407 _110796 P Q) = (term408 _110796 P Q).
Proof. exact (@lem4811527 _110796 P Q). Qed.
Lemma lem4811529 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term421 _110796 _110799 x y x' s r f) = (term422 _110796 _110799 x y x' s r f).
Proof. exact (@lem4811528 _110796 (term221 _110796 _110799 s r x f y) (term370 _110796 _110799 x' s r f)). Qed.
Lemma lem4811530 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term423 _110796 _110799 x s r f y) = (term369 _110796 _110799 x y s r f).
Proof. exact (eq_refl (term423 _110796 _110799 x s r f y)). Qed.
Lemma lem4811531 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term424 _110796 _110799 x s r f) = (term370 _110796 _110799 x s r f).
Proof. exact (fun_ext (fun y : _110796 => @lem4811530 _110796 _110799 x y s r f)). Qed.
Lemma lem4811532 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811533 {_110796 _110799 : Type'} (x : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term425 _110796 _110799 x s r f) = (term371 _110796 _110799 x s r f).
Proof. exact (MK_COMB (@lem4811532 _110796) (@lem4811531 _110796 _110799 x s r f)). Qed.
Lemma lem4811534 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term401 _110796 _110799 s r x f y) = (term401 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term401 _110796 _110799 s r x f y)). Qed.
Lemma lem4811535 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term421 _110796 _110799 x y x' s r f) = (term417 _110796 _110799 x y x' s r f).
Proof. exact (MK_COMB (@lem4811534 _110796 _110799 s r x f y) (@lem4811533 _110796 _110799 x' s r f)). Qed.
Lemma lem4811536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811537 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term426 _110796 _110799 x y x' s r f) = (term427 _110796 _110799 x y x' s r f).
Proof. exact (MK_COMB (@lem4811536) (@lem4811535 _110796 _110799 x y x' s r f)). Qed.
Lemma lem4811538 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term423 _110796 _110799 x s r f y) = (term369 _110796 _110799 x y s r f).
Proof. exact (eq_refl (term423 _110796 _110799 x s r f y)). Qed.
Lemma lem4811539 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term401 _110796 _110799 s r x f y) = (term401 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term401 _110796 _110799 s r x f y)). Qed.
Lemma lem4811540 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term428 _110796 _110799 x y x' s r f y') = (term429 _110796 _110799 x y x' y' s r f).
Proof. exact (MK_COMB (@lem4811539 _110796 _110799 s r x f y) (@lem4811538 _110796 _110799 x' y' s r f)). Qed.
Lemma lem4811541 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term430 _110796 _110799 x y x' s r f) = (term431 _110796 _110799 x y x' s r f).
Proof. exact (fun_ext (fun y' : _110796 => @lem4811540 _110796 _110799 x y x' y' s r f)). Qed.
Lemma lem4811542 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811543 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term422 _110796 _110799 x y x' s r f) = (term432 _110796 _110799 x y x' s r f).
Proof. exact (MK_COMB (@lem4811542 _110796) (@lem4811541 _110796 _110799 x y x' s r f)). Qed.
Lemma lem4811544 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term421 _110796 _110799 x y x' s r f) = (term422 _110796 _110799 x y x' s r f)) = ((term417 _110796 _110799 x y x' s r f) = (term432 _110796 _110799 x y x' s r f)).
Proof. exact (MK_COMB (@lem4811537 _110796 _110799 x y x' s r f) (@lem4811543 _110796 _110799 x y x' s r f)). Qed.
Lemma lem4811545 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term417 _110796 _110799 x y x' s r f) = (term432 _110796 _110799 x y x' s r f).
Proof. exact (EQ_MP (@lem4811544 _110796 _110799 x y x' s r f) (@lem4811529 _110796 _110799 x y x' s r f)). Qed.
Lemma lem4811547 {A : Type'} (P : Prop) (Q : A -> Prop) : (term407 A P Q) = (term408 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4811548 {_110799 : Type'} (P : Prop) (Q : _110799 -> Prop) : (term407 _110799 P Q) = (term408 _110799 P Q).
Proof. exact (@lem4811547 _110799 P Q). Qed.
Lemma lem4811549 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term433 _110796 _110799 x y x' y' s r f) = (term434 _110796 _110799 x y x' y' s r f).
Proof. exact (@lem4811548 _110799 (term221 _110796 _110799 s r x f y) (term368 _110796 _110799 x' y' s r f)). Qed.
Lemma lem4811550 {_110796 _110799 : Type'} (x : _110799) (x' : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term435 _110796 _110799 x' y s r f x) = (term367 _110796 _110799 x x' y s r f).
Proof. exact (eq_refl (term435 _110796 _110799 x' y s r f x)). Qed.
Lemma lem4811551 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term436 _110796 _110799 x y s r f) = (term368 _110796 _110799 x y s r f).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811550 _110796 _110799 x' x y s r f)). Qed.
Lemma lem4811552 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811553 {_110796 _110799 : Type'} (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term437 _110796 _110799 x y s r f) = (term369 _110796 _110799 x y s r f).
Proof. exact (MK_COMB (@lem4811552 _110799) (@lem4811551 _110796 _110799 x y s r f)). Qed.
Lemma lem4811554 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term401 _110796 _110799 s r x f y) = (term401 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term401 _110796 _110799 s r x f y)). Qed.
Lemma lem4811555 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term433 _110796 _110799 x y x' y' s r f) = (term429 _110796 _110799 x y x' y' s r f).
Proof. exact (MK_COMB (@lem4811554 _110796 _110799 s r x f y) (@lem4811553 _110796 _110799 x' y' s r f)). Qed.
Lemma lem4811556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811557 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term438 _110796 _110799 x y x' y' s r f) = (term439 _110796 _110799 x y x' y' s r f).
Proof. exact (MK_COMB (@lem4811556) (@lem4811555 _110796 _110799 x y x' y' s r f)). Qed.
Lemma lem4811558 {_110796 _110799 : Type'} (x' : _110799) (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term435 _110796 _110799 x y s r f x') = (term367 _110796 _110799 x' x y s r f).
Proof. exact (eq_refl (term435 _110796 _110799 x y s r f x')). Qed.
Lemma lem4811559 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term401 _110796 _110799 s r x f y) = (term401 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term401 _110796 _110799 s r x f y)). Qed.
Lemma lem4811560 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110799) (x'' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term440 _110796 _110799 x y x'' y' s r f x') = (term441 _110796 _110799 x y x' x'' y' s r f).
Proof. exact (MK_COMB (@lem4811559 _110796 _110799 s r x f y) (@lem4811558 _110796 _110799 x' x'' y' s r f)). Qed.
Lemma lem4811561 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term442 _110796 _110799 x y x' y' s r f) = (term443 _110796 _110799 x y x' y' s r f).
Proof. exact (fun_ext (fun x'' : _110799 => @lem4811560 _110796 _110799 x y x'' x' y' s r f)). Qed.
Lemma lem4811562 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811563 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term434 _110796 _110799 x y x' y' s r f) = (term444 _110796 _110799 x y x' y' s r f).
Proof. exact (MK_COMB (@lem4811562 _110799) (@lem4811561 _110796 _110799 x y x' y' s r f)). Qed.
Lemma lem4811564 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term433 _110796 _110799 x y x' y' s r f) = (term434 _110796 _110799 x y x' y' s r f)) = ((term429 _110796 _110799 x y x' y' s r f) = (term444 _110796 _110799 x y x' y' s r f)).
Proof. exact (MK_COMB (@lem4811557 _110796 _110799 x y x' y' s r f) (@lem4811563 _110796 _110799 x y x' y' s r f)). Qed.
Lemma lem4811565 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term429 _110796 _110799 x y x' y' s r f) = (term444 _110796 _110799 x y x' y' s r f).
Proof. exact (EQ_MP (@lem4811564 _110796 _110799 x y x' y' s r f) (@lem4811549 _110796 _110799 x y x' y' s r f)). Qed.
Lemma lem4811567 {A : Type'} (P : Prop) (Q : A -> Prop) : (term407 A P Q) = (term408 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4811568 {_110799 : Type'} (P : Prop) (Q : _110799 -> Prop) : (term407 _110799 P Q) = (term408 _110799 P Q).
Proof. exact (@lem4811567 _110799 P Q). Qed.
Lemma lem4811569 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110799) (x'' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term445 _110796 _110799 x y x' x'' y' s r f) = (term446 _110796 _110799 x y x' x'' y' s r f).
Proof. exact (@lem4811568 _110799 (term221 _110796 _110799 s r x f y) (term366 _110796 _110799 x' x'' y' s r f)). Qed.
Lemma lem4811570 {_110796 _110799 : Type'} (x' : _110799) (x'' : _110799) (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term447 _110796 _110799 x' x y s r f x'') = (term364 _110796 _110799 x' x'' x y s r f).
Proof. exact (eq_refl (term447 _110796 _110799 x' x y s r f x'')). Qed.
Lemma lem4811571 {_110796 _110799 : Type'} (x' : _110799) (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term448 _110796 _110799 x' x y s r f) = (term366 _110796 _110799 x' x y s r f).
Proof. exact (fun_ext (fun x'' : _110799 => @lem4811570 _110796 _110799 x' x'' x y s r f)). Qed.
Lemma lem4811572 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811573 {_110796 _110799 : Type'} (x' : _110799) (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term449 _110796 _110799 x' x y s r f) = (term367 _110796 _110799 x' x y s r f).
Proof. exact (MK_COMB (@lem4811572 _110799) (@lem4811571 _110796 _110799 x' x y s r f)). Qed.
Lemma lem4811574 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term401 _110796 _110799 s r x f y) = (term401 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term401 _110796 _110799 s r x f y)). Qed.
Lemma lem4811575 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110799) (x'' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term445 _110796 _110799 x y x' x'' y' s r f) = (term441 _110796 _110799 x y x' x'' y' s r f).
Proof. exact (MK_COMB (@lem4811574 _110796 _110799 s r x f y) (@lem4811573 _110796 _110799 x' x'' y' s r f)). Qed.
Lemma lem4811576 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811577 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110799) (x'' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term450 _110796 _110799 x y x' x'' y' s r f) = (term451 _110796 _110799 x y x' x'' y' s r f).
Proof. exact (MK_COMB (@lem4811576) (@lem4811575 _110796 _110799 x y x' x'' y' s r f)). Qed.
Lemma lem4811578 {_110796 _110799 : Type'} (x' : _110799) (x'' : _110799) (x : _110796) (y : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term447 _110796 _110799 x' x y s r f x'') = (term364 _110796 _110799 x' x'' x y s r f).
Proof. exact (eq_refl (term447 _110796 _110799 x' x y s r f x'')). Qed.
Lemma lem4811579 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term401 _110796 _110799 s r x f y) = (term401 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term401 _110796 _110799 s r x f y)). Qed.
Lemma lem4811580 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110799) (x'' : _110799) (x''' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term452 _110796 _110799 x y x' x''' y' s r f x'') = (term453 _110796 _110799 x y x' x'' x''' y' s r f).
Proof. exact (MK_COMB (@lem4811579 _110796 _110799 s r x f y) (@lem4811578 _110796 _110799 x' x'' x''' y' s r f)). Qed.
Lemma lem4811581 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110799) (x'' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term454 _110796 _110799 x y x' x'' y' s r f) = (term455 _110796 _110799 x y x' x'' y' s r f).
Proof. exact (fun_ext (fun x''' : _110799 => @lem4811580 _110796 _110799 x y x' x''' x'' y' s r f)). Qed.
Lemma lem4811582 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811583 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110799) (x'' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term446 _110796 _110799 x y x' x'' y' s r f) = (term456 _110796 _110799 x y x' x'' y' s r f).
Proof. exact (MK_COMB (@lem4811582 _110799) (@lem4811581 _110796 _110799 x y x' x'' y' s r f)). Qed.
Lemma lem4811584 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110799) (x'' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : ((term445 _110796 _110799 x y x' x'' y' s r f) = (term446 _110796 _110799 x y x' x'' y' s r f)) = ((term441 _110796 _110799 x y x' x'' y' s r f) = (term456 _110796 _110799 x y x' x'' y' s r f)).
Proof. exact (MK_COMB (@lem4811577 _110796 _110799 x y x' x'' y' s r f) (@lem4811583 _110796 _110799 x y x' x'' y' s r f)). Qed.
Lemma lem4811585 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110799) (x'' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term441 _110796 _110799 x y x' x'' y' s r f) = (term456 _110796 _110799 x y x' x'' y' s r f).
Proof. exact (EQ_MP (@lem4811584 _110796 _110799 x y x' x'' y' s r f) (@lem4811569 _110796 _110799 x y x' x'' y' s r f)). Qed.
Lemma lem4811586 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term443 _110796 _110799 x y x' y' s r f) = (term457 _110796 _110799 x y x' y' s r f).
Proof. exact (fun_ext (fun x'' : _110799 => @lem4811585 _110796 _110799 x y x'' x' y' s r f)). Qed.
Lemma lem4811587 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811588 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term444 _110796 _110799 x y x' y' s r f) = (term458 _110796 _110799 x y x' y' s r f).
Proof. exact (MK_COMB (@lem4811587 _110799) (@lem4811586 _110796 _110799 x y x' y' s r f)). Qed.
Lemma lem4811589 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term429 _110796 _110799 x y x' y' s r f) = (term458 _110796 _110799 x y x' y' s r f).
Proof. exact (TRANS (@lem4811565 _110796 _110799 x y x' y' s r f) (@lem4811588 _110796 _110799 x y x' y' s r f)). Qed.
Lemma lem4811590 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term431 _110796 _110799 x y x' s r f) = (term459 _110796 _110799 x y x' s r f).
Proof. exact (fun_ext (fun y' : _110796 => @lem4811589 _110796 _110799 x y x' y' s r f)). Qed.
Lemma lem4811591 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811592 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term432 _110796 _110799 x y x' s r f) = (term460 _110796 _110799 x y x' s r f).
Proof. exact (MK_COMB (@lem4811591 _110796) (@lem4811590 _110796 _110799 x y x' s r f)). Qed.
Lemma lem4811593 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term417 _110796 _110799 x y x' s r f) = (term460 _110796 _110799 x y x' s r f).
Proof. exact (TRANS (@lem4811545 _110796 _110799 x y x' s r f) (@lem4811592 _110796 _110799 x y x' s r f)). Qed.
Lemma lem4811594 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term419 _110796 _110799 x y s r f) = (term461 _110796 _110799 x y s r f).
Proof. exact (fun_ext (fun x' : _110796 => @lem4811593 _110796 _110799 x y x' s r f)). Qed.
Lemma lem4811595 {_110796 : Type'} : (@ex _110796) = (@ex _110796).
Proof. exact (eq_refl (@ex _110796)). Qed.
Lemma lem4811596 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term420 _110796 _110799 x y s r f) = (term462 _110796 _110799 x y s r f).
Proof. exact (MK_COMB (@lem4811595 _110796) (@lem4811594 _110796 _110799 x y s r f)). Qed.
Lemma lem4811597 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term403 _110796 _110799 x y s r f) = (term462 _110796 _110799 x y s r f).
Proof. exact (TRANS (@lem4811525 _110796 _110799 x y s r f) (@lem4811596 _110796 _110799 x y s r f)). Qed.
Lemma lem4811598 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term405 _110796 _110799 x s r f) = (term463 _110796 _110799 x s r f).
Proof. exact (fun_ext (fun y : _110799 => @lem4811597 _110796 _110799 x y s r f)). Qed.
Lemma lem4811599 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811600 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term406 _110796 _110799 x s r f) = (term464 _110796 _110799 x s r f).
Proof. exact (MK_COMB (@lem4811599 _110799) (@lem4811598 _110796 _110799 x s r f)). Qed.
Lemma lem4811601 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term388 _110796 _110799 x s r f) = (term464 _110796 _110799 x s r f).
Proof. exact (TRANS (@lem4811505 _110796 _110799 x s r f) (@lem4811600 _110796 _110799 x s r f)). Qed.
Lemma lem4811602 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term390 _110796 _110799 s r f) = (term465 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4811601 _110796 _110799 x s r f)). Qed.
Lemma lem4811603 {_110799 : Type'} : (@ex _110799) = (@ex _110799).
Proof. exact (eq_refl (@ex _110799)). Qed.
Lemma lem4811604 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term391 _110796 _110799 s r f) = (term466 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811603 _110799) (@lem4811602 _110796 _110799 s r f)). Qed.
Lemma lem4811605 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term374 _110796 _110799 s r f) = (term466 _110796 _110799 s r f).
Proof. exact (TRANS (@lem4811479 _110796 _110799 s r f) (@lem4811604 _110796 _110799 s r f)). Qed.
Lemma lem4811607 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term198 _110796 _110799 s r f) = (term466 _110796 _110799 s r f).
Proof. exact (TRANS (@lem4811453 _110796 _110799 s r f) (@lem4811605 _110796 _110799 s r f)). Qed.
Lemma lem4811608 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term94 _110796 _110799 s r f) = (term466 _110796 _110799 s r f).
Proof. exact (TRANS (@lem4810754 _110796 _110799 s r f) (@lem4811607 _110796 _110799 s r f)). Qed.
Lemma lem4811609 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term94 _110796 _110799 s r f) : term466 _110796 _110799 s r f.
Proof. exact (EQ_MP (@lem4811608 _110796 _110799 s r f) (@lem4810559 _110796 _110799 s r f h1)). Qed.
Lemma lem4811610 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term464 _110796 _110799 x s r f) : term464 _110796 _110799 x s r f.
Proof. exact (h1). Qed.
Lemma lem4811611 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term462 _110796 _110799 x y s r f) : term462 _110796 _110799 x y s r f.
Proof. exact (h1). Qed.
Lemma lem4811612 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term460 _110796 _110799 x y x' s r f) : term460 _110796 _110799 x y x' s r f.
Proof. exact (h1). Qed.
Lemma lem4811613 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term458 _110796 _110799 x y x' y' s r f) : term458 _110796 _110799 x y x' y' s r f.
Proof. exact (h1). Qed.
Lemma lem4811614 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x'' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term456 _110796 _110799 x y x'' x' y' s r f) : term456 _110796 _110799 x y x'' x' y' s r f.
Proof. exact (h1). Qed.
Lemma lem4811615 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term453 _110796 _110799 x y x'' x''' x' y' s r f) : term453 _110796 _110799 x y x'' x''' x' y' s r f.
Proof. exact (h1). Qed.
Lemma lem4811664 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term168 _110796 _110799 s r x f y) = (term168 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term168 _110796 _110799 s r x f y)). Qed.
Lemma lem4811665 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term176 _110796 _110799 s r x f) = (term176 _110796 _110799 s r x f).
Proof. exact (fun_ext (fun y : _110799 => @lem4811664 _110796 _110799 s r x f y)). Qed.
Lemma lem4811666 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811667 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term177 _110796 _110799 s r x f) = (term177 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4811666 _110799) (@lem4811665 _110796 _110799 s r x f)). Qed.
Lemma lem4811668 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term185 _110796 _110799 s r f) = (term185 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4811667 _110796 _110799 s r x f)). Qed.
Lemma lem4811669 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811670 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term186 _110796 _110799 s r f) = (term186 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4811669 _110799) (@lem4811668 _110796 _110799 s r f)). Qed.
Lemma lem4811725 {_110796 _110799 : Type'} (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y' : _110796) : (term362 _110796 _110799 x'' f x''' s r x' y') = (term362 _110796 _110799 x'' f x''' s r x' y').
Proof. exact (eq_refl (term362 _110796 _110799 x'' f x''' s r x' y')). Qed.
Lemma lem4811726 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term364 _110796 _110799 x'' x''' x' y' s r f) = (term364 _110796 _110799 x'' x''' x' y' s r f).
Proof. exact (MK_COMB (@lem4811725 _110796 _110799 x'' f x''' s r x' y') (@lem4811670 _110796 _110799 s r f)). Qed.
Lemma lem4811777 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term162 _110796 _110799 s r x f y) = (term162 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term162 _110796 _110799 s r x f y)). Qed.
Lemma lem4811782 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4811787 {_110796 : Type'} (x : _110796) (y : _110796) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4811806 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term96 _110796 _110799 y f x s) = (term96 _110796 _110799 y f x s).
Proof. exact (eq_refl (term96 _110796 _110799 y f x s)). Qed.
Lemma lem4811807 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term104 _110796 _110799 y f s) = (term104 _110796 _110799 y f s).
Proof. exact (fun_ext (fun x : _110799 => @lem4811806 _110796 _110799 y f x s)). Qed.
Lemma lem4811808 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811809 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term105 _110796 _110799 y f s) = (term105 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4811808 _110799) (@lem4811807 _110796 _110799 y f s)). Qed.
Lemma lem4811810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811811 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term108 _110796 _110799 y f s) = (term108 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4811810) (@lem4811809 _110796 _110799 y f s)). Qed.
Lemma lem4811812 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term110 _110796 _110799 f s x y) = (term110 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811811 _110796 _110799 y f s) (@lem4811787 _110796 x y)). Qed.
Lemma lem4811831 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term96 _110796 _110799 x f x' s) = (term96 _110796 _110799 x f x' s).
Proof. exact (eq_refl (term96 _110796 _110799 x f x' s)). Qed.
Lemma lem4811832 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term104 _110796 _110799 x f s) = (term104 _110796 _110799 x f s).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811831 _110796 _110799 x f x' s)). Qed.
Lemma lem4811833 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811834 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term105 _110796 _110799 x f s) = (term105 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4811833 _110799) (@lem4811832 _110796 _110799 x f s)). Qed.
Lemma lem4811835 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811836 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term108 _110796 _110799 x f s) = (term108 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4811835) (@lem4811834 _110796 _110799 x f s)). Qed.
Lemma lem4811837 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term113 _110796 _110799 f s x y) = (term113 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811836 _110796 _110799 x f s) (@lem4811812 _110796 _110799 f s x y)). Qed.
Lemma lem4811838 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811839 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term120 _110796 _110799 f s x y) = (term120 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811838) (@lem4811837 _110796 _110799 f s x y)). Qed.
Lemma lem4811840 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term122 _110796 _110799 f s r x y) = (term122 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811839 _110796 _110799 f s x y) (@lem4811782 _110796 r x y)). Qed.
Lemma lem4811841 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term132 _110796 _110799 f s r x) = (term132 _110796 _110799 f s r x).
Proof. exact (fun_ext (fun y : _110796 => @lem4811840 _110796 _110799 f s r x y)). Qed.
Lemma lem4811842 {_110796 : Type'} : (@all _110796) = (@all _110796).
Proof. exact (eq_refl (@all _110796)). Qed.
Lemma lem4811843 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term133 _110796 _110799 f s r x) = (term133 _110796 _110799 f s r x).
Proof. exact (MK_COMB (@lem4811842 _110796) (@lem4811841 _110796 _110799 f s r x)). Qed.
Lemma lem4811844 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term141 _110796 _110799 f s r) = (term141 _110796 _110799 f s r).
Proof. exact (fun_ext (fun x : _110796 => @lem4811843 _110796 _110799 f s r x)). Qed.
Lemma lem4811845 {_110796 : Type'} : (@all _110796) = (@all _110796).
Proof. exact (eq_refl (@all _110796)). Qed.
Lemma lem4811846 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term142 _110796 _110799 f s r) = (term142 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4811845 _110796) (@lem4811844 _110796 _110799 f s r)). Qed.
Lemma lem4811847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4811848 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term192 _110796 _110799 f s r) = (term192 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4811847) (@lem4811846 _110796 _110799 f s r)). Qed.
Lemma lem4811849 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term221 _110796 _110799 s r x f y) = (term221 _110796 _110799 s r x f y).
Proof. exact (MK_COMB (@lem4811848 _110796 _110799 f s r) (@lem4811777 _110796 _110799 s r x f y)). Qed.
Lemma lem4811850 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811851 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term401 _110796 _110799 s r x f y) = (term401 _110796 _110799 s r x f y).
Proof. exact (MK_COMB (@lem4811850) (@lem4811849 _110796 _110799 s r x f y)). Qed.
Lemma lem4811852 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term453 _110796 _110799 x y x'' x''' x' y' s r f) = (term453 _110796 _110799 x y x'' x''' x' y' s r f).
Proof. exact (MK_COMB (@lem4811851 _110796 _110799 s r x f y) (@lem4811726 _110796 _110799 x'' x''' x' y' s r f)). Qed.
Lemma lem4811853 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term453 _110796 _110799 x y x'' x''' x' y' s r f) : term453 _110796 _110799 x y x'' x''' x' y' s r f.
Proof. exact (EQ_MP (@lem4811852 _110796 _110799 x y x'' x''' x' y' s r f) (@lem4811615 _110796 _110799 x y x'' x''' x' y' s r f h1)). Qed.
Lemma lem4811854 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term221 _110796 _110799 s r x f y.
Proof. exact (h1). Qed.
Lemma lem4811855 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term364 _110796 _110799 x'' x''' x' y' s r f.
Proof. exact (h1). Qed.
Lemma lem4811856 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term162 _110796 _110799 s r x f y.
Proof. exact (proj2 (@lem4811854 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4811857 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term142 _110796 _110799 f s r.
Proof. exact (proj1 (@lem4811854 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4811858 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term154 _110796 _110799 r x f y.
Proof. exact (proj2 (@lem4811856 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4811859 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term164 _110799 s x y.
Proof. exact (proj1 (@lem4811856 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4811862 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term150 _110799 s x y.
Proof. exact (proj2 (@lem4811859 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4811866 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term186 _110796 _110799 s r f.
Proof. exact (proj2 (@lem4811855 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4811867 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term296 _110796 _110799 x'' f x''' s r x' y'.
Proof. exact (proj1 (@lem4811855 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4811869 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term262 _110796 _110799 x'' f x''' s x' y'.
Proof. exact (proj1 (@lem4811867 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4811870 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term240 _110796 _110799 f x''' s x' y'.
Proof. exact (proj2 (@lem4811869 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4811871 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term91 _110796 _110799 x' f x'' s.
Proof. exact (proj1 (@lem4811869 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4811873 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term91 _110796 _110799 y' f x''' s.
Proof. exact (proj1 (@lem4811870 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4811879 {A : Type'} (P : A -> Prop) (Q : Prop) : (term467 A P Q) = (term468 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4811880 {_110799 : Type'} (P : _110799 -> Prop) (Q : Prop) : (term467 _110799 P Q) = (term468 _110799 P Q).
Proof. exact (@lem4811879 _110799 P Q). Qed.
Lemma lem4811881 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term469 _110796 _110799 f s x y) = (term470 _110796 _110799 f s x y).
Proof. exact (@lem4811880 _110799 (term104 _110796 _110799 y f s) (x = y)). Qed.
Lemma lem4811882 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term471 _110796 _110799 y f s x) = (term96 _110796 _110799 y f x s).
Proof. exact (eq_refl (term471 _110796 _110799 y f s x)). Qed.
Lemma lem4811883 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term472 _110796 _110799 y f s) = (term104 _110796 _110799 y f s).
Proof. exact (fun_ext (fun x : _110799 => @lem4811882 _110796 _110799 y f x s)). Qed.
Lemma lem4811884 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811885 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term473 _110796 _110799 y f s) = (term105 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4811884 _110799) (@lem4811883 _110796 _110799 y f s)). Qed.
Lemma lem4811886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811887 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term474 _110796 _110799 y f s) = (term108 _110796 _110799 y f s).
Proof. exact (MK_COMB (@lem4811886) (@lem4811885 _110796 _110799 y f s)). Qed.
Lemma lem4811888 {_110796 : Type'} (x : _110796) (y : _110796) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4811889 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term469 _110796 _110799 f s x y) = (term110 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811887 _110796 _110799 y f s) (@lem4811888 _110796 x y)). Qed.
Lemma lem4811890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811891 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term475 _110796 _110799 f s x y) = (term476 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811890) (@lem4811889 _110796 _110799 f s x y)). Qed.
Lemma lem4811892 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term471 _110796 _110799 y f s x) = (term96 _110796 _110799 y f x s).
Proof. exact (eq_refl (term471 _110796 _110799 y f s x)). Qed.
Lemma lem4811893 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811894 {_110796 _110799 : Type'} (y : _110796) (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) : (term477 _110796 _110799 y f s x) = (term478 _110796 _110799 y f x s).
Proof. exact (MK_COMB (@lem4811893) (@lem4811892 _110796 _110799 y f x s)). Qed.
Lemma lem4811895 {_110796 : Type'} (x : _110796) (y : _110796) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4811896 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term479 _110796 _110799 f s x x' y) = (term480 _110796 _110799 f x s x' y).
Proof. exact (MK_COMB (@lem4811894 _110796 _110799 y f x s) (@lem4811895 _110796 x' y)). Qed.
Lemma lem4811897 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term481 _110796 _110799 f s x y) = (term482 _110796 _110799 f s x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811896 _110796 _110799 f x' s x y)). Qed.
Lemma lem4811898 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811899 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term470 _110796 _110799 f s x y) = (term483 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811898 _110799) (@lem4811897 _110796 _110799 f s x y)). Qed.
Lemma lem4811900 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : ((term469 _110796 _110799 f s x y) = (term470 _110796 _110799 f s x y)) = ((term110 _110796 _110799 f s x y) = (term483 _110796 _110799 f s x y)).
Proof. exact (MK_COMB (@lem4811891 _110796 _110799 f s x y) (@lem4811899 _110796 _110799 f s x y)). Qed.
Lemma lem4811901 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term110 _110796 _110799 f s x y) = (term483 _110796 _110799 f s x y).
Proof. exact (EQ_MP (@lem4811900 _110796 _110799 f s x y) (@lem4811881 _110796 _110799 f s x y)). Qed.
Lemma lem4811902 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term108 _110796 _110799 x f s) = (term108 _110796 _110799 x f s).
Proof. exact (eq_refl (term108 _110796 _110799 x f s)). Qed.
Lemma lem4811903 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term113 _110796 _110799 f s x y) = (term484 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811902 _110796 _110799 x f s) (@lem4811901 _110796 _110799 f s x y)). Qed.
Lemma lem4811905 {A : Type'} (P : A -> Prop) (Q : Prop) : (term467 A P Q) = (term468 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4811906 {_110799 : Type'} (P : _110799 -> Prop) (Q : Prop) : (term467 _110799 P Q) = (term468 _110799 P Q).
Proof. exact (@lem4811905 _110799 P Q). Qed.
Lemma lem4811907 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term485 _110796 _110799 f s x y) = (term486 _110796 _110799 f s x y).
Proof. exact (@lem4811906 _110799 (term104 _110796 _110799 x f s) (term483 _110796 _110799 f s x y)). Qed.
Lemma lem4811908 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term471 _110796 _110799 x f s x') = (term96 _110796 _110799 x f x' s).
Proof. exact (eq_refl (term471 _110796 _110799 x f s x')). Qed.
Lemma lem4811909 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term472 _110796 _110799 x f s) = (term104 _110796 _110799 x f s).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811908 _110796 _110799 x f x' s)). Qed.
Lemma lem4811910 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811911 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term473 _110796 _110799 x f s) = (term105 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4811910 _110799) (@lem4811909 _110796 _110799 x f s)). Qed.
Lemma lem4811912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811913 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (s : _110799 -> Prop) : (term474 _110796 _110799 x f s) = (term108 _110796 _110799 x f s).
Proof. exact (MK_COMB (@lem4811912) (@lem4811911 _110796 _110799 x f s)). Qed.
Lemma lem4811914 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term483 _110796 _110799 f s x y) = (term483 _110796 _110799 f s x y).
Proof. exact (eq_refl (term483 _110796 _110799 f s x y)). Qed.
Lemma lem4811915 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term485 _110796 _110799 f s x y) = (term484 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811913 _110796 _110799 x f s) (@lem4811914 _110796 _110799 f s x y)). Qed.
Lemma lem4811916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811917 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term487 _110796 _110799 f s x y) = (term488 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811916) (@lem4811915 _110796 _110799 f s x y)). Qed.
Lemma lem4811918 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term471 _110796 _110799 x f s x') = (term96 _110796 _110799 x f x' s).
Proof. exact (eq_refl (term471 _110796 _110799 x f s x')). Qed.
Lemma lem4811919 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811920 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term477 _110796 _110799 x f s x') = (term478 _110796 _110799 x f x' s).
Proof. exact (MK_COMB (@lem4811919) (@lem4811918 _110796 _110799 x f x' s)). Qed.
Lemma lem4811921 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term483 _110796 _110799 f s x y) = (term483 _110796 _110799 f s x y).
Proof. exact (eq_refl (term483 _110796 _110799 f s x y)). Qed.
Lemma lem4811922 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term489 _110796 _110799 x f s x' y) = (term490 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811920 _110796 _110799 x' f x s) (@lem4811921 _110796 _110799 f s x' y)). Qed.
Lemma lem4811923 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term491 _110796 _110799 f s x y) = (term492 _110796 _110799 f s x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811922 _110796 _110799 x' f s x y)). Qed.
Lemma lem4811924 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811925 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term486 _110796 _110799 f s x y) = (term493 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811924 _110799) (@lem4811923 _110796 _110799 f s x y)). Qed.
Lemma lem4811926 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : ((term485 _110796 _110799 f s x y) = (term486 _110796 _110799 f s x y)) = ((term484 _110796 _110799 f s x y) = (term493 _110796 _110799 f s x y)).
Proof. exact (MK_COMB (@lem4811917 _110796 _110799 f s x y) (@lem4811925 _110796 _110799 f s x y)). Qed.
Lemma lem4811927 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term484 _110796 _110799 f s x y) = (term493 _110796 _110799 f s x y).
Proof. exact (EQ_MP (@lem4811926 _110796 _110799 f s x y) (@lem4811907 _110796 _110799 f s x y)). Qed.
Lemma lem4811929 {A : Type'} (P : Prop) (Q : A -> Prop) : (term494 A P Q) = (term495 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4811930 {_110799 : Type'} (P : Prop) (Q : _110799 -> Prop) : (term494 _110799 P Q) = (term495 _110799 P Q).
Proof. exact (@lem4811929 _110799 P Q). Qed.
Lemma lem4811931 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term496 _110796 _110799 x f s x' y) = (term497 _110796 _110799 x f s x' y).
Proof. exact (@lem4811930 _110799 (term96 _110796 _110799 x' f x s) (term482 _110796 _110799 f s x' y)). Qed.
Lemma lem4811932 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x : _110799) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term498 _110796 _110799 f s x' y x) = (term480 _110796 _110799 f x s x' y).
Proof. exact (eq_refl (term498 _110796 _110799 f s x' y x)). Qed.
Lemma lem4811933 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term499 _110796 _110799 f s x y) = (term482 _110796 _110799 f s x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811932 _110796 _110799 f x' s x y)). Qed.
Lemma lem4811934 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811935 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term500 _110796 _110799 f s x y) = (term483 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811934 _110799) (@lem4811933 _110796 _110799 f s x y)). Qed.
Lemma lem4811936 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term478 _110796 _110799 x f x' s) = (term478 _110796 _110799 x f x' s).
Proof. exact (eq_refl (term478 _110796 _110799 x f x' s)). Qed.
Lemma lem4811937 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term496 _110796 _110799 x f s x' y) = (term490 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811936 _110796 _110799 x' f x s) (@lem4811935 _110796 _110799 f s x' y)). Qed.
Lemma lem4811938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811939 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term501 _110796 _110799 x f s x' y) = (term502 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811938) (@lem4811937 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811940 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term498 _110796 _110799 f s x y x') = (term480 _110796 _110799 f x' s x y).
Proof. exact (eq_refl (term498 _110796 _110799 f s x y x')). Qed.
Lemma lem4811941 {_110796 _110799 : Type'} (x : _110796) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) : (term478 _110796 _110799 x f x' s) = (term478 _110796 _110799 x f x' s).
Proof. exact (eq_refl (term478 _110796 _110799 x f x' s)). Qed.
Lemma lem4811942 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (x'' : _110796) (y : _110796) : (term503 _110796 _110799 x f s x'' y x') = (term504 _110796 _110799 x f x' s x'' y).
Proof. exact (MK_COMB (@lem4811941 _110796 _110799 x'' f x s) (@lem4811940 _110796 _110799 f x' s x'' y)). Qed.
Lemma lem4811943 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term505 _110796 _110799 x f s x' y) = (term506 _110796 _110799 x f s x' y).
Proof. exact (fun_ext (fun x'' : _110799 => @lem4811942 _110796 _110799 x f x'' s x' y)). Qed.
Lemma lem4811944 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811945 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term497 _110796 _110799 x f s x' y) = (term507 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811944 _110799) (@lem4811943 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811946 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : ((term496 _110796 _110799 x f s x' y) = (term497 _110796 _110799 x f s x' y)) = ((term490 _110796 _110799 x f s x' y) = (term507 _110796 _110799 x f s x' y)).
Proof. exact (MK_COMB (@lem4811939 _110796 _110799 x f s x' y) (@lem4811945 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811947 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term490 _110796 _110799 x f s x' y) = (term507 _110796 _110799 x f s x' y).
Proof. exact (EQ_MP (@lem4811946 _110796 _110799 x f s x' y) (@lem4811931 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811948 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term492 _110796 _110799 f s x y) = (term508 _110796 _110799 f s x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811947 _110796 _110799 x' f s x y)). Qed.
Lemma lem4811949 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811950 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term493 _110796 _110799 f s x y) = (term509 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811949 _110799) (@lem4811948 _110796 _110799 f s x y)). Qed.
Lemma lem4811951 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term484 _110796 _110799 f s x y) = (term509 _110796 _110799 f s x y).
Proof. exact (TRANS (@lem4811927 _110796 _110799 f s x y) (@lem4811950 _110796 _110799 f s x y)). Qed.
Lemma lem4811952 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term113 _110796 _110799 f s x y) = (term509 _110796 _110799 f s x y).
Proof. exact (TRANS (@lem4811903 _110796 _110799 f s x y) (@lem4811951 _110796 _110799 f s x y)). Qed.
Lemma lem4811953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811954 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term120 _110796 _110799 f s x y) = (term510 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811953) (@lem4811952 _110796 _110799 f s x y)). Qed.
Lemma lem4811955 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4811956 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term122 _110796 _110799 f s r x y) = (term511 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811954 _110796 _110799 f s x y) (@lem4811955 _110796 r x y)). Qed.
Lemma lem4811958 {A : Type'} (P : A -> Prop) (Q : Prop) : (term467 A P Q) = (term468 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4811959 {_110799 : Type'} (P : _110799 -> Prop) (Q : Prop) : (term467 _110799 P Q) = (term468 _110799 P Q).
Proof. exact (@lem4811958 _110799 P Q). Qed.
Lemma lem4811960 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term512 _110796 _110799 f s r x y) = (term513 _110796 _110799 f s r x y).
Proof. exact (@lem4811959 _110799 (term508 _110796 _110799 f s x y) (r x y)). Qed.
Lemma lem4811961 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term514 _110796 _110799 f s x' y x) = (term507 _110796 _110799 x f s x' y).
Proof. exact (eq_refl (term514 _110796 _110799 f s x' y x)). Qed.
Lemma lem4811962 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term515 _110796 _110799 f s x y) = (term508 _110796 _110799 f s x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811961 _110796 _110799 x' f s x y)). Qed.
Lemma lem4811963 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811964 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term516 _110796 _110799 f s x y) = (term509 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811963 _110799) (@lem4811962 _110796 _110799 f s x y)). Qed.
Lemma lem4811965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811966 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (x : _110796) (y : _110796) : (term517 _110796 _110799 f s x y) = (term510 _110796 _110799 f s x y).
Proof. exact (MK_COMB (@lem4811965) (@lem4811964 _110796 _110799 f s x y)). Qed.
Lemma lem4811967 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4811968 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term512 _110796 _110799 f s r x y) = (term511 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811966 _110796 _110799 f s x y) (@lem4811967 _110796 r x y)). Qed.
Lemma lem4811969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811970 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term518 _110796 _110799 f s r x y) = (term519 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811969) (@lem4811968 _110796 _110799 f s r x y)). Qed.
Lemma lem4811971 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term514 _110796 _110799 f s x' y x) = (term507 _110796 _110799 x f s x' y).
Proof. exact (eq_refl (term514 _110796 _110799 f s x' y x)). Qed.
Lemma lem4811972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811973 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term520 _110796 _110799 f s x' y x) = (term521 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811972) (@lem4811971 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811974 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4811975 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term522 _110796 _110799 f s x r x' y) = (term523 _110796 _110799 x f s r x' y).
Proof. exact (MK_COMB (@lem4811973 _110796 _110799 x f s x' y) (@lem4811974 _110796 r x' y)). Qed.
Lemma lem4811976 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term524 _110796 _110799 f s r x y) = (term525 _110796 _110799 f s r x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4811975 _110796 _110799 x' f s r x y)). Qed.
Lemma lem4811977 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811978 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term513 _110796 _110799 f s r x y) = (term526 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4811977 _110799) (@lem4811976 _110796 _110799 f s r x y)). Qed.
Lemma lem4811979 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : ((term512 _110796 _110799 f s r x y) = (term513 _110796 _110799 f s r x y)) = ((term511 _110796 _110799 f s r x y) = (term526 _110796 _110799 f s r x y)).
Proof. exact (MK_COMB (@lem4811970 _110796 _110799 f s r x y) (@lem4811978 _110796 _110799 f s r x y)). Qed.
Lemma lem4811980 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term511 _110796 _110799 f s r x y) = (term526 _110796 _110799 f s r x y).
Proof. exact (EQ_MP (@lem4811979 _110796 _110799 f s r x y) (@lem4811960 _110796 _110799 f s r x y)). Qed.
Lemma lem4811982 {A : Type'} (P : A -> Prop) (Q : Prop) : (term467 A P Q) = (term468 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4811983 {_110799 : Type'} (P : _110799 -> Prop) (Q : Prop) : (term467 _110799 P Q) = (term468 _110799 P Q).
Proof. exact (@lem4811982 _110799 P Q). Qed.
Lemma lem4811984 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term527 _110796 _110799 x f s r x' y) = (term528 _110796 _110799 x f s r x' y).
Proof. exact (@lem4811983 _110799 (term506 _110796 _110799 x f s x' y) (r x' y)). Qed.
Lemma lem4811985 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (x'' : _110796) (y : _110796) : (term529 _110796 _110799 x f s x'' y x') = (term504 _110796 _110799 x f x' s x'' y).
Proof. exact (eq_refl (term529 _110796 _110799 x f s x'' y x')). Qed.
Lemma lem4811986 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term530 _110796 _110799 x f s x' y) = (term506 _110796 _110799 x f s x' y).
Proof. exact (fun_ext (fun x'' : _110799 => @lem4811985 _110796 _110799 x f x'' s x' y)). Qed.
Lemma lem4811987 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4811988 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term531 _110796 _110799 x f s x' y) = (term507 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811987 _110799) (@lem4811986 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811989 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811990 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (x' : _110796) (y : _110796) : (term532 _110796 _110799 x f s x' y) = (term521 _110796 _110799 x f s x' y).
Proof. exact (MK_COMB (@lem4811989) (@lem4811988 _110796 _110799 x f s x' y)). Qed.
Lemma lem4811991 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4811992 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term527 _110796 _110799 x f s r x' y) = (term523 _110796 _110799 x f s r x' y).
Proof. exact (MK_COMB (@lem4811990 _110796 _110799 x f s x' y) (@lem4811991 _110796 r x' y)). Qed.
Lemma lem4811993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4811994 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term533 _110796 _110799 x f s r x' y) = (term534 _110796 _110799 x f s r x' y).
Proof. exact (MK_COMB (@lem4811993) (@lem4811992 _110796 _110799 x f s r x' y)). Qed.
Lemma lem4811995 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (x'' : _110796) (y : _110796) : (term529 _110796 _110799 x f s x'' y x') = (term504 _110796 _110799 x f x' s x'' y).
Proof. exact (eq_refl (term529 _110796 _110799 x f s x'' y x')). Qed.
Lemma lem4811996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4811997 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (x'' : _110796) (y : _110796) : (term535 _110796 _110799 x f s x'' y x') = (term536 _110796 _110799 x f x' s x'' y).
Proof. exact (MK_COMB (@lem4811996) (@lem4811995 _110796 _110799 x f x' s x'' y)). Qed.
Lemma lem4811998 {_110796 : Type'} (r : type1402 _110796) (x : _110796) (y : _110796) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4811999 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (x'' : _110796) (y : _110796) : (term537 _110796 _110799 x f s x' r x'' y) = (term538 _110796 _110799 x f x' s r x'' y).
Proof. exact (MK_COMB (@lem4811997 _110796 _110799 x f x' s x'' y) (@lem4811998 _110796 r x'' y)). Qed.
Lemma lem4812000 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term539 _110796 _110799 x f s r x' y) = (term540 _110796 _110799 x f s r x' y).
Proof. exact (fun_ext (fun x'' : _110799 => @lem4811999 _110796 _110799 x f x'' s r x' y)). Qed.
Lemma lem4812001 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4812002 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term528 _110796 _110799 x f s r x' y) = (term541 _110796 _110799 x f s r x' y).
Proof. exact (MK_COMB (@lem4812001 _110799) (@lem4812000 _110796 _110799 x f s r x' y)). Qed.
Lemma lem4812003 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : ((term527 _110796 _110799 x f s r x' y) = (term528 _110796 _110799 x f s r x' y)) = ((term523 _110796 _110799 x f s r x' y) = (term541 _110796 _110799 x f s r x' y)).
Proof. exact (MK_COMB (@lem4811994 _110796 _110799 x f s r x' y) (@lem4812002 _110796 _110799 x f s r x' y)). Qed.
Lemma lem4812004 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term523 _110796 _110799 x f s r x' y) = (term541 _110796 _110799 x f s r x' y).
Proof. exact (EQ_MP (@lem4812003 _110796 _110799 x f s r x' y) (@lem4811984 _110796 _110799 x f s r x' y)). Qed.
Lemma lem4812005 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term525 _110796 _110799 f s r x y) = (term542 _110796 _110799 f s r x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4812004 _110796 _110799 x' f s r x y)). Qed.
Lemma lem4812006 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4812007 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term526 _110796 _110799 f s r x y) = (term543 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4812006 _110799) (@lem4812005 _110796 _110799 f s r x y)). Qed.
Lemma lem4812008 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term511 _110796 _110799 f s r x y) = (term543 _110796 _110799 f s r x y).
Proof. exact (TRANS (@lem4811980 _110796 _110799 f s r x y) (@lem4812007 _110796 _110799 f s r x y)). Qed.
Lemma lem4812009 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term122 _110796 _110799 f s r x y) = (term543 _110796 _110799 f s r x y).
Proof. exact (TRANS (@lem4811956 _110796 _110799 f s r x y) (@lem4812008 _110796 _110799 f s r x y)). Qed.
Lemma lem4812010 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term132 _110796 _110799 f s r x) = (term544 _110796 _110799 f s r x).
Proof. exact (fun_ext (fun y : _110796 => @lem4812009 _110796 _110799 f s r x y)). Qed.
Lemma lem4812011 {_110796 : Type'} : (@all _110796) = (@all _110796).
Proof. exact (eq_refl (@all _110796)). Qed.
Lemma lem4812012 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term133 _110796 _110799 f s r x) = (term545 _110796 _110799 f s r x).
Proof. exact (MK_COMB (@lem4812011 _110796) (@lem4812010 _110796 _110799 f s r x)). Qed.
Lemma lem4812013 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term141 _110796 _110799 f s r) = (term546 _110796 _110799 f s r).
Proof. exact (fun_ext (fun x : _110796 => @lem4812012 _110796 _110799 f s r x)). Qed.
Lemma lem4812014 {_110796 : Type'} : (@all _110796) = (@all _110796).
Proof. exact (eq_refl (@all _110796)). Qed.
Lemma lem4812015 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term142 _110796 _110799 f s r) = (term547 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4812014 _110796) (@lem4812013 _110796 _110799 f s r)). Qed.
Lemma lem4812046 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (x' : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (x'' : _110796) (y : _110796) : (term538 _110796 _110799 x f x' s r x'' y) = (term538 _110796 _110799 x f x' s r x'' y).
Proof. exact (eq_refl (term538 _110796 _110799 x f x' s r x'' y)). Qed.
Lemma lem4812047 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term540 _110796 _110799 x f s r x' y) = (term540 _110796 _110799 x f s r x' y).
Proof. exact (fun_ext (fun x'' : _110799 => @lem4812046 _110796 _110799 x f x'' s r x' y)). Qed.
Lemma lem4812048 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4812049 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x' : _110796) (y : _110796) : (term541 _110796 _110799 x f s r x' y) = (term541 _110796 _110799 x f s r x' y).
Proof. exact (MK_COMB (@lem4812048 _110799) (@lem4812047 _110796 _110799 x f s r x' y)). Qed.
Lemma lem4812050 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term542 _110796 _110799 f s r x y) = (term542 _110796 _110799 f s r x y).
Proof. exact (fun_ext (fun x' : _110799 => @lem4812049 _110796 _110799 x' f s r x y)). Qed.
Lemma lem4812051 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4812052 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) (y : _110796) : (term543 _110796 _110799 f s r x y) = (term543 _110796 _110799 f s r x y).
Proof. exact (MK_COMB (@lem4812051 _110799) (@lem4812050 _110796 _110799 f s r x y)). Qed.
Lemma lem4812053 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term544 _110796 _110799 f s r x) = (term544 _110796 _110799 f s r x).
Proof. exact (fun_ext (fun y : _110796 => @lem4812052 _110796 _110799 f s r x y)). Qed.
Lemma lem4812054 {_110796 : Type'} : (@all _110796) = (@all _110796).
Proof. exact (eq_refl (@all _110796)). Qed.
Lemma lem4812055 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110796) : (term545 _110796 _110799 f s r x) = (term545 _110796 _110799 f s r x).
Proof. exact (MK_COMB (@lem4812054 _110796) (@lem4812053 _110796 _110799 f s r x)). Qed.
Lemma lem4812056 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term546 _110796 _110799 f s r) = (term546 _110796 _110799 f s r).
Proof. exact (fun_ext (fun x : _110796 => @lem4812055 _110796 _110799 f s r x)). Qed.
Lemma lem4812057 {_110796 : Type'} : (@all _110796) = (@all _110796).
Proof. exact (eq_refl (@all _110796)). Qed.
Lemma lem4812058 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term547 _110796 _110799 f s r) = (term547 _110796 _110799 f s r).
Proof. exact (MK_COMB (@lem4812057 _110796) (@lem4812056 _110796 _110799 f s r)). Qed.
Lemma lem4812059 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) : (term142 _110796 _110799 f s r) = (term547 _110796 _110799 f s r).
Proof. exact (TRANS (@lem4812015 _110796 _110799 f s r) (@lem4812058 _110796 _110799 f s r)). Qed.
Lemma lem4812060 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term547 _110796 _110799 f s r.
Proof. exact (EQ_MP (@lem4812059 _110796 _110799 f s r) (@lem4811857 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4812106 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term168 _110796 _110799 s r x f y) = (term168 _110796 _110799 s r x f y).
Proof. exact (eq_refl (term168 _110796 _110799 s r x f y)). Qed.
Lemma lem4812107 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term176 _110796 _110799 s r x f) = (term176 _110796 _110799 s r x f).
Proof. exact (fun_ext (fun y : _110799 => @lem4812106 _110796 _110799 s r x f y)). Qed.
Lemma lem4812108 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4812109 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) : (term177 _110796 _110799 s r x f) = (term177 _110796 _110799 s r x f).
Proof. exact (MK_COMB (@lem4812108 _110799) (@lem4812107 _110796 _110799 s r x f)). Qed.
Lemma lem4812110 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term185 _110796 _110799 s r f) = (term185 _110796 _110799 s r f).
Proof. exact (fun_ext (fun x : _110799 => @lem4812109 _110796 _110799 s r x f)). Qed.
Lemma lem4812111 {_110799 : Type'} : (@all _110799) = (@all _110799).
Proof. exact (eq_refl (@all _110799)). Qed.
Lemma lem4812113 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term186 _110796 _110799 s r f) = (term186 _110796 _110799 s r f).
Proof. exact (MK_COMB (@lem4812111 _110799) (@lem4812110 _110796 _110799 s r f)). Qed.
Lemma lem4812114 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term186 _110796 _110799 s r f.
Proof. exact (EQ_MP (@lem4812113 _110796 _110799 s r f) (@lem4811866 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812139 {_110796 _110799 : Type'} (_59648 : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term548 _110796 _110799 f s r _59648.
Proof. exact (@lem4812060 _110796 _110799 s r x f y h1 _59648). Qed.
Lemma lem4812140 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) : (term548 _110796 _110799 f s r _59648) = (term545 _110796 _110799 f s r _59648).
Proof. exact (eq_refl (term548 _110796 _110799 f s r _59648)). Qed.
Lemma lem4812141 {_110796 _110799 : Type'} (_59648 : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term545 _110796 _110799 f s r _59648.
Proof. exact (EQ_MP (@lem4812140 _110796 _110799 f s r _59648) (@lem4812139 _110796 _110799 _59648 s r x f y h1)). Qed.
Lemma lem4812142 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term549 _110796 _110799 f s r _59648 _59649.
Proof. exact (@lem4812141 _110796 _110799 _59648 s r x f y h1 _59649). Qed.
Lemma lem4812143 {_110796 _110799 : Type'} (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term549 _110796 _110799 f s r _59648 _59649) = (term543 _110796 _110799 f s r _59648 _59649).
Proof. exact (eq_refl (term549 _110796 _110799 f s r _59648 _59649)). Qed.
Lemma lem4812144 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term543 _110796 _110799 f s r _59648 _59649.
Proof. exact (EQ_MP (@lem4812143 _110796 _110799 f s r _59648 _59649) (@lem4812142 _110796 _110799 _59648 _59649 s r x f y h1)). Qed.
Lemma lem4812145 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (_59650 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term550 _110796 _110799 f s r _59648 _59649 _59650.
Proof. exact (@lem4812144 _110796 _110799 _59648 _59649 s r x f y h1 _59650). Qed.
Lemma lem4812146 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term550 _110796 _110799 f s r _59648 _59649 _59650) = (term541 _110796 _110799 _59650 f s r _59648 _59649).
Proof. exact (eq_refl (term550 _110796 _110799 f s r _59648 _59649 _59650)). Qed.
Lemma lem4812147 {_110796 _110799 : Type'} (_59650 : _110799) (_59648 : _110796) (_59649 : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term541 _110796 _110799 _59650 f s r _59648 _59649.
Proof. exact (EQ_MP (@lem4812146 _110796 _110799 _59650 f s r _59648 _59649) (@lem4812145 _110796 _110799 _59648 _59649 _59650 s r x f y h1)). Qed.
Lemma lem4812148 {_110796 _110799 : Type'} (_59650 : _110799) (_59648 : _110796) (_59649 : _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term551 _110796 _110799 _59650 f s r _59648 _59649 _59651.
Proof. exact (@lem4812147 _110796 _110799 _59650 _59648 _59649 s r x f y h1 _59651). Qed.
Lemma lem4812149 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term551 _110796 _110799 _59650 f s r _59648 _59649 _59651) = (term538 _110796 _110799 _59650 f _59651 s r _59648 _59649).
Proof. exact (eq_refl (term551 _110796 _110799 _59650 f s r _59648 _59649 _59651)). Qed.
Lemma lem4812150 {_110796 _110799 : Type'} (_59650 : _110799) (_59651 : _110799) (_59648 : _110796) (_59649 : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term538 _110796 _110799 _59650 f _59651 s r _59648 _59649.
Proof. exact (EQ_MP (@lem4812149 _110796 _110799 _59650 f _59651 s r _59648 _59649) (@lem4812148 _110796 _110799 _59650 _59648 _59649 _59651 s r x f y h1)). Qed.
Lemma lem4812151 {_110796 _110799 : Type'} (_59652 : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term552 _110796 _110799 s r f _59652.
Proof. exact (@lem4812114 _110796 _110799 x'' x''' x' y' s r f h1 _59652). Qed.
Lemma lem4812152 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) : (term552 _110796 _110799 s r f _59652) = (term177 _110796 _110799 s r _59652 f).
Proof. exact (eq_refl (term552 _110796 _110799 s r f _59652)). Qed.
Lemma lem4812153 {_110796 _110799 : Type'} (_59652 : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term177 _110796 _110799 s r _59652 f.
Proof. exact (EQ_MP (@lem4812152 _110796 _110799 s r _59652 f) (@lem4812151 _110796 _110799 _59652 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812154 {_110796 _110799 : Type'} (_59652 : _110799) (_59653 : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term553 _110796 _110799 s r _59652 f _59653.
Proof. exact (@lem4812153 _110796 _110799 _59652 x'' x''' x' y' s r f h1 _59653). Qed.
Lemma lem4812155 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term553 _110796 _110799 s r _59652 f _59653) = (term168 _110796 _110799 s r _59652 f _59653).
Proof. exact (eq_refl (term553 _110796 _110799 s r _59652 f _59653)). Qed.
Lemma lem4812156 {_110796 _110799 : Type'} (_59652 : _110799) (_59653 : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term168 _110796 _110799 s r _59652 f _59653.
Proof. exact (EQ_MP (@lem4812155 _110796 _110799 s r _59652 f _59653) (@lem4812154 _110796 _110799 _59652 _59653 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812160 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term538 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term554 _110796 _110799 _59650 f _59651 s r _59648 _59649).
Proof. exact (@lem4810027 (term96 _110796 _110799 _59648 f _59650 s) (term480 _110796 _110799 f _59651 s _59648 _59649) (r _59648 _59649)). Qed.
Lemma lem4812161 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term555 _110796 _110799 f _59651 s r _59648 _59649) = (term556 _110796 _110799 f _59651 s r _59648 _59649).
Proof. exact (@lem4810027 (term96 _110796 _110799 _59649 f _59651 s) (_59648 = _59649) (r _59648 _59649)). Qed.
Lemma lem4812172 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term556 _110796 _110799 f _59651 s r _59648 _59649) = (term557 _110796 _110799 f _59651 s r _59648 _59649).
Proof. exact (@lem4810027 (term558 _110796 _110799 _59649 f _59651) (term559 _110799 _59651 s) (term560 _110796 r _59648 _59649)). Qed.
Lemma lem4812173 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term555 _110796 _110799 f _59651 s r _59648 _59649) = (term557 _110796 _110799 f _59651 s r _59648 _59649).
Proof. exact (TRANS (@lem4812161 _110796 _110799 f _59651 s r _59648 _59649) (@lem4812172 _110796 _110799 f _59651 s r _59648 _59649)). Qed.
Lemma lem4812174 {_110796 _110799 : Type'} (_59648 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (s : _110799 -> Prop) : (term478 _110796 _110799 _59648 f _59650 s) = (term478 _110796 _110799 _59648 f _59650 s).
Proof. exact (eq_refl (term478 _110796 _110799 _59648 f _59650 s)). Qed.
Lemma lem4812175 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term554 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term561 _110796 _110799 _59650 f _59651 s r _59648 _59649).
Proof. exact (MK_COMB (@lem4812174 _110796 _110799 _59648 f _59650 s) (@lem4812173 _110796 _110799 f _59651 s r _59648 _59649)). Qed.
Lemma lem4812182 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term561 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term562 _110796 _110799 _59650 f _59651 s r _59648 _59649).
Proof. exact (@lem4810027 (term558 _110796 _110799 _59648 f _59650) (term559 _110799 _59650 s) (term557 _110796 _110799 f _59651 s r _59648 _59649)). Qed.
Lemma lem4812183 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term554 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term562 _110796 _110799 _59650 f _59651 s r _59648 _59649).
Proof. exact (TRANS (@lem4812175 _110796 _110799 _59650 f _59651 s r _59648 _59649) (@lem4812182 _110796 _110799 _59650 f _59651 s r _59648 _59649)). Qed.
Lemma lem4812185 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term538 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term562 _110796 _110799 _59650 f _59651 s r _59648 _59649).
Proof. exact (TRANS (@lem4812160 _110796 _110799 _59650 f _59651 s r _59648 _59649) (@lem4812183 _110796 _110799 _59650 f _59651 s r _59648 _59649)). Qed.
Lemma lem4812186 {_110796 _110799 : Type'} (_59650 : _110799) (_59651 : _110799) (_59648 : _110796) (_59649 : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term562 _110796 _110799 _59650 f _59651 s r _59648 _59649.
Proof. exact (EQ_MP (@lem4812185 _110796 _110799 _59650 f _59651 s r _59648 _59649) (@lem4812150 _110796 _110799 _59650 _59651 _59648 _59649 s r x f y h1)). Qed.
Lemma lem4812190 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term563 _110796 _110799 r x f y.
Proof. exact (proj2 (@lem4811858 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4812204 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term168 _110796 _110799 s r _59652 f _59653) = (term564 _110796 _110799 s r _59652 f _59653).
Proof. exact (@lem4810027 (term559 _110799 _59652 s) (term145 _110799 s _59652 _59653) (term159 _110796 _110799 r _59652 f _59653)). Qed.
Lemma lem4812211 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term565 _110796 _110799 s r _59652 f _59653) = (term566 _110796 _110799 s r _59652 f _59653).
Proof. exact (@lem4810027 (term559 _110799 _59653 s) (_59652 = _59653) (term159 _110796 _110799 r _59652 f _59653)). Qed.
Lemma lem4812212 {_110799 : Type'} (_59652 : _110799) (s : _110799 -> Prop) : (term143 _110799 _59652 s) = (term143 _110799 _59652 s).
Proof. exact (eq_refl (term143 _110799 _59652 s)). Qed.
Lemma lem4812215 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term564 _110796 _110799 s r _59652 f _59653) = (term567 _110796 _110799 s r _59652 f _59653).
Proof. exact (MK_COMB (@lem4812212 _110799 _59652 s) (@lem4812211 _110796 _110799 s r _59652 f _59653)). Qed.
Lemma lem4812217 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term168 _110796 _110799 s r _59652 f _59653) = (term567 _110796 _110799 s r _59652 f _59653).
Proof. exact (TRANS (@lem4812204 _110796 _110799 s r _59652 f _59653) (@lem4812215 _110796 _110799 s r _59652 f _59653)). Qed.
Lemma lem4812220 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term115 _110796 r x' y'.
Proof. exact (proj2 (@lem4811867 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812222 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term24 _110796 x' y'.
Proof. exact (proj2 (@lem4811870 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812228 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : x' = (f x'').
Proof. exact (proj1 (@lem4811871 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812259 {_110796 : Type'} (r : type1402 _110796) (y' : _110796) : (term568 _110796 r y') = (term568 _110796 r y').
Proof. exact (eq_refl (term568 _110796 r y')). Qed.
Lemma lem4812260 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : (term569 _110796 r y' x') = (term570 _110796 _110799 r y' f x'').
Proof. exact (MK_COMB (@lem4812259 _110796 r y') (@lem4812228 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812261 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : (term570 _110796 _110799 r y' f x'') = (term571 _110796 _110799 r f x'' y').
Proof. exact (eq_refl (term570 _110796 _110799 r y' f x'')). Qed.
Lemma lem4812262 {_110796 : Type'} (r : type1402 _110796) (y' : _110796) (x' : _110796) : (term572 _110796 r y' x') = (term572 _110796 r y' x').
Proof. exact (eq_refl (term572 _110796 r y' x')). Qed.
Lemma lem4812263 {_110796 _110799 : Type'} (x' : _110796) (r : type1402 _110796) (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : ((term569 _110796 r y' x') = (term570 _110796 _110799 r y' f x'')) = ((term569 _110796 r y' x') = (term571 _110796 _110799 r f x'' y')).
Proof. exact (MK_COMB (@lem4812262 _110796 r y' x') (@lem4812261 _110796 _110799 r f x'' y')). Qed.
Lemma lem4812264 {_110796 : Type'} (r : type1402 _110796) (x' : _110796) (y' : _110796) : (term569 _110796 r y' x') = (term115 _110796 r x' y').
Proof. exact (eq_refl (term569 _110796 r y' x')). Qed.
Lemma lem4812265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4812266 {_110796 : Type'} (r : type1402 _110796) (x' : _110796) (y' : _110796) : (term572 _110796 r y' x') = (term573 _110796 r x' y').
Proof. exact (MK_COMB (@lem4812265) (@lem4812264 _110796 r x' y')). Qed.
Lemma lem4812267 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : (term571 _110796 _110799 r f x'' y') = (term571 _110796 _110799 r f x'' y').
Proof. exact (eq_refl (term571 _110796 _110799 r f x'' y')). Qed.
Lemma lem4812268 {_110796 _110799 : Type'} (x' : _110796) (r : type1402 _110796) (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : ((term569 _110796 r y' x') = (term571 _110796 _110799 r f x'' y')) = ((term115 _110796 r x' y') = (term571 _110796 _110799 r f x'' y')).
Proof. exact (MK_COMB (@lem4812266 _110796 r x' y') (@lem4812267 _110796 _110799 r f x'' y')). Qed.
Lemma lem4812269 {_110796 _110799 : Type'} (x' : _110796) (r : type1402 _110796) (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : ((term569 _110796 r y' x') = (term570 _110796 _110799 r y' f x'')) = ((term115 _110796 r x' y') = (term571 _110796 _110799 r f x'' y')).
Proof. exact (TRANS (@lem4812263 _110796 _110799 x' r f x'' y') (@lem4812268 _110796 _110799 x' r f x'' y')). Qed.
Lemma lem4812270 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : (term115 _110796 r x' y') = (term571 _110796 _110799 r f x'' y').
Proof. exact (EQ_MP (@lem4812269 _110796 _110799 x' r f x'' y') (@lem4812260 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812271 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term571 _110796 _110799 r f x'' y'.
Proof. exact (EQ_MP (@lem4812270 _110796 _110799 x'' x''' x' y' s r f h1) (@lem4812220 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812272 {_110796 : Type'} (y' : _110796) : (term574 _110796 y') = (term574 _110796 y').
Proof. exact (eq_refl (term574 _110796 y')). Qed.
Lemma lem4812273 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : (term575 _110796 y' x') = (term576 _110796 _110799 y' f x'').
Proof. exact (MK_COMB (@lem4812272 _110796 y') (@lem4812228 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812274 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : (term576 _110796 _110799 y' f x'') = (term577 _110796 _110799 f x'' y').
Proof. exact (eq_refl (term576 _110796 _110799 y' f x'')). Qed.
Lemma lem4812275 {_110796 : Type'} (y' : _110796) (x' : _110796) : (term578 _110796 y' x') = (term578 _110796 y' x').
Proof. exact (eq_refl (term578 _110796 y' x')). Qed.
Lemma lem4812276 {_110796 _110799 : Type'} (x' : _110796) (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : ((term575 _110796 y' x') = (term576 _110796 _110799 y' f x'')) = ((term575 _110796 y' x') = (term577 _110796 _110799 f x'' y')).
Proof. exact (MK_COMB (@lem4812275 _110796 y' x') (@lem4812274 _110796 _110799 f x'' y')). Qed.
Lemma lem4812277 {_110796 : Type'} (x' : _110796) (y' : _110796) : (term575 _110796 y' x') = (term24 _110796 x' y').
Proof. exact (eq_refl (term575 _110796 y' x')). Qed.
Lemma lem4812278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4812279 {_110796 : Type'} (x' : _110796) (y' : _110796) : (term578 _110796 y' x') = (term579 _110796 x' y').
Proof. exact (MK_COMB (@lem4812278) (@lem4812277 _110796 x' y')). Qed.
Lemma lem4812280 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : (term577 _110796 _110799 f x'' y') = (term577 _110796 _110799 f x'' y').
Proof. exact (eq_refl (term577 _110796 _110799 f x'' y')). Qed.
Lemma lem4812281 {_110796 _110799 : Type'} (x' : _110796) (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : ((term575 _110796 y' x') = (term577 _110796 _110799 f x'' y')) = ((term24 _110796 x' y') = (term577 _110796 _110799 f x'' y')).
Proof. exact (MK_COMB (@lem4812279 _110796 x' y') (@lem4812280 _110796 _110799 f x'' y')). Qed.
Lemma lem4812282 {_110796 _110799 : Type'} (x' : _110796) (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : ((term575 _110796 y' x') = (term576 _110796 _110799 y' f x'')) = ((term24 _110796 x' y') = (term577 _110796 _110799 f x'' y')).
Proof. exact (TRANS (@lem4812276 _110796 _110799 x' f x'' y') (@lem4812281 _110796 _110799 x' f x'' y')). Qed.
Lemma lem4812283 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : (term24 _110796 x' y') = (term577 _110796 _110799 f x'' y').
Proof. exact (EQ_MP (@lem4812282 _110796 _110799 x' f x'' y') (@lem4812273 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812284 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term577 _110796 _110799 f x'' y'.
Proof. exact (EQ_MP (@lem4812283 _110796 _110799 x'' x''' x' y' s r f h1) (@lem4812222 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812298 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : y' = (f x''').
Proof. exact (proj1 (@lem4811873 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812354 {_110796 _110799 : Type'} (_59652 : _110799) (_59653 : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term567 _110796 _110799 s r _59652 f _59653.
Proof. exact (EQ_MP (@lem4812217 _110796 _110799 s r _59652 f _59653) (@lem4812156 _110796 _110799 _59652 _59653 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812355 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (x'' : _110799) : (term580 _110796 _110799 r f x'') = (term580 _110796 _110799 r f x'').
Proof. exact (eq_refl (term580 _110796 _110799 r f x'')). Qed.
Lemma lem4812356 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : (term581 _110796 _110799 r f x'' y') = (term582 _110796 _110799 r x'' f x''').
Proof. exact (MK_COMB (@lem4812355 _110796 _110799 r f x'') (@lem4812298 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812357 {_110796 _110799 : Type'} (r : type1402 _110796) (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : (term582 _110796 _110799 r x'' f x''') = (term563 _110796 _110799 r x'' f x''').
Proof. exact (eq_refl (term582 _110796 _110799 r x'' f x''')). Qed.
Lemma lem4812358 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : (term583 _110796 _110799 r f x'' y') = (term583 _110796 _110799 r f x'' y').
Proof. exact (eq_refl (term583 _110796 _110799 r f x'' y')). Qed.
Lemma lem4812359 {_110796 _110799 : Type'} (y' : _110796) (r : type1402 _110796) (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : ((term581 _110796 _110799 r f x'' y') = (term582 _110796 _110799 r x'' f x''')) = ((term581 _110796 _110799 r f x'' y') = (term563 _110796 _110799 r x'' f x''')).
Proof. exact (MK_COMB (@lem4812358 _110796 _110799 r f x'' y') (@lem4812357 _110796 _110799 r x'' f x''')). Qed.
Lemma lem4812360 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : (term581 _110796 _110799 r f x'' y') = (term571 _110796 _110799 r f x'' y').
Proof. exact (eq_refl (term581 _110796 _110799 r f x'' y')). Qed.
Lemma lem4812361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4812362 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : (term583 _110796 _110799 r f x'' y') = (term584 _110796 _110799 r f x'' y').
Proof. exact (MK_COMB (@lem4812361) (@lem4812360 _110796 _110799 r f x'' y')). Qed.
Lemma lem4812363 {_110796 _110799 : Type'} (r : type1402 _110796) (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : (term563 _110796 _110799 r x'' f x''') = (term563 _110796 _110799 r x'' f x''').
Proof. exact (eq_refl (term563 _110796 _110799 r x'' f x''')). Qed.
Lemma lem4812364 {_110796 _110799 : Type'} (y' : _110796) (r : type1402 _110796) (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : ((term581 _110796 _110799 r f x'' y') = (term563 _110796 _110799 r x'' f x''')) = ((term571 _110796 _110799 r f x'' y') = (term563 _110796 _110799 r x'' f x''')).
Proof. exact (MK_COMB (@lem4812362 _110796 _110799 r f x'' y') (@lem4812363 _110796 _110799 r x'' f x''')). Qed.
Lemma lem4812365 {_110796 _110799 : Type'} (y' : _110796) (r : type1402 _110796) (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : ((term581 _110796 _110799 r f x'' y') = (term582 _110796 _110799 r x'' f x''')) = ((term571 _110796 _110799 r f x'' y') = (term563 _110796 _110799 r x'' f x''')).
Proof. exact (TRANS (@lem4812359 _110796 _110799 y' r x'' f x''') (@lem4812364 _110796 _110799 y' r x'' f x''')). Qed.
Lemma lem4812366 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : (term571 _110796 _110799 r f x'' y') = (term563 _110796 _110799 r x'' f x''').
Proof. exact (EQ_MP (@lem4812365 _110796 _110799 y' r x'' f x''') (@lem4812356 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812368 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x'' : _110799) : (term585 _110796 _110799 f x'') = (term585 _110796 _110799 f x'').
Proof. exact (eq_refl (term585 _110796 _110799 f x'')). Qed.
Lemma lem4812369 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : (term586 _110796 _110799 f x'' y') = (term587 _110796 _110799 x'' f x''').
Proof. exact (MK_COMB (@lem4812368 _110796 _110799 f x'') (@lem4812298 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812370 {_110796 _110799 : Type'} (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : (term587 _110796 _110799 x'' f x''') = (term155 _110796 _110799 x'' f x''').
Proof. exact (eq_refl (term587 _110796 _110799 x'' f x''')). Qed.
Lemma lem4812371 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : (term588 _110796 _110799 f x'' y') = (term588 _110796 _110799 f x'' y').
Proof. exact (eq_refl (term588 _110796 _110799 f x'' y')). Qed.
Lemma lem4812372 {_110796 _110799 : Type'} (y' : _110796) (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : ((term586 _110796 _110799 f x'' y') = (term587 _110796 _110799 x'' f x''')) = ((term586 _110796 _110799 f x'' y') = (term155 _110796 _110799 x'' f x''')).
Proof. exact (MK_COMB (@lem4812371 _110796 _110799 f x'' y') (@lem4812370 _110796 _110799 x'' f x''')). Qed.
Lemma lem4812373 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : (term586 _110796 _110799 f x'' y') = (term577 _110796 _110799 f x'' y').
Proof. exact (eq_refl (term586 _110796 _110799 f x'' y')). Qed.
Lemma lem4812374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4812375 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x'' : _110799) (y' : _110796) : (term588 _110796 _110799 f x'' y') = (term589 _110796 _110799 f x'' y').
Proof. exact (MK_COMB (@lem4812374) (@lem4812373 _110796 _110799 f x'' y')). Qed.
Lemma lem4812376 {_110796 _110799 : Type'} (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : (term155 _110796 _110799 x'' f x''') = (term155 _110796 _110799 x'' f x''').
Proof. exact (eq_refl (term155 _110796 _110799 x'' f x''')). Qed.
Lemma lem4812377 {_110796 _110799 : Type'} (y' : _110796) (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : ((term586 _110796 _110799 f x'' y') = (term155 _110796 _110799 x'' f x''')) = ((term577 _110796 _110799 f x'' y') = (term155 _110796 _110799 x'' f x''')).
Proof. exact (MK_COMB (@lem4812375 _110796 _110799 f x'' y') (@lem4812376 _110796 _110799 x'' f x''')). Qed.
Lemma lem4812378 {_110796 _110799 : Type'} (y' : _110796) (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : ((term586 _110796 _110799 f x'' y') = (term587 _110796 _110799 x'' f x''')) = ((term577 _110796 _110799 f x'' y') = (term155 _110796 _110799 x'' f x''')).
Proof. exact (TRANS (@lem4812372 _110796 _110799 y' x'' f x''') (@lem4812377 _110796 _110799 y' x'' f x''')). Qed.
Lemma lem4812379 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : (term577 _110796 _110799 f x'' y') = (term155 _110796 _110799 x'' f x''').
Proof. exact (EQ_MP (@lem4812378 _110796 _110799 y' x'' f x''') (@lem4812369 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812380 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term155 _110796 _110799 x'' f x'''.
Proof. exact (EQ_MP (@lem4812379 _110796 _110799 x'' x''' x' y' s r f h1) (@lem4812284 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4812462 {_110796 : Type'} (x : _110796) : x = x.
Proof. exact (@lem21386 _110796 x). Qed.
Lemma lem4812463 {_110796 : Type'} (x : _110796) : x = x.
Proof. exact (@lem4812462 _110796 x). Qed.
Lemma lem4812464 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x : _110799) : (f x) = (f x).
Proof. exact (@lem4812463 _110796 (f x)). Qed.
Lemma lem4812465 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x : _110799) : term590 _110796 _110799 f x.
Proof. exact (fun h0 : term591 _110796 _110799 f x => @lem4812464 _110796 _110799 f x). Qed.
Lemma lem4812467 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4812468 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x : _110799) : (term590 _110796 _110799 f x) = ((f x) = (f x)).
Proof. exact (@lem4812467 ((f x) = (f x))). Qed.
Lemma lem4812469 {_110796 _110799 : Type'} (f : _110799 -> _110796) (x : _110799) : (f x) = (f x).
Proof. exact (EQ_MP (@lem4812468 _110796 _110799 f x) (@lem4812465 _110796 _110799 f x)). Qed.
Lemma lem4812471 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : @IN _110799 x s.
Proof. exact (proj1 (@lem4811859 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4812472 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term593 _110799 x s.
Proof. exact (fun h0 : term559 _110799 x s => @lem4812471 _110796 _110799 s r x f y h1). Qed.
Lemma lem4812474 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4812475 {_110799 : Type'} (x : _110799) (s : _110799 -> Prop) : (term593 _110799 x s) = (@IN _110799 x s).
Proof. exact (@lem4812474 (@IN _110799 x s)). Qed.
Lemma lem4812476 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : @IN _110799 x s.
Proof. exact (EQ_MP (@lem4812475 _110799 x s) (@lem4812472 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4812478 {_110796 : Type'} (x : _110796) : x = x.
Proof. exact (@lem21386 _110796 x). Qed.
Lemma lem4812479 {_110796 : Type'} (x : _110796) : x = x.
Proof. exact (@lem4812478 _110796 x). Qed.
Lemma lem4812480 {_110796 _110799 : Type'} (f : _110799 -> _110796) (y : _110799) : (f y) = (f y).
Proof. exact (@lem4812479 _110796 (f y)). Qed.
Lemma lem4812481 {_110796 _110799 : Type'} (f : _110799 -> _110796) (y : _110799) : term590 _110796 _110799 f y.
Proof. exact (fun h0 : term591 _110796 _110799 f y => @lem4812480 _110796 _110799 f y). Qed.
Lemma lem4812483 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4812484 {_110796 _110799 : Type'} (f : _110799 -> _110796) (y : _110799) : (term590 _110796 _110799 f y) = ((f y) = (f y)).
Proof. exact (@lem4812483 ((f y) = (f y))). Qed.
Lemma lem4812485 {_110796 _110799 : Type'} (f : _110799 -> _110796) (y : _110799) : (f y) = (f y).
Proof. exact (EQ_MP (@lem4812484 _110796 _110799 f y) (@lem4812481 _110796 _110799 f y)). Qed.
Lemma lem4812487 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : @IN _110799 y s.
Proof. exact (proj1 (@lem4811862 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4812488 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term593 _110799 y s.
Proof. exact (fun h0 : term559 _110799 y s => @lem4812487 _110796 _110799 s r x f y h1). Qed.
Lemma lem4812490 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4812491 {_110799 : Type'} (y : _110799) (s : _110799 -> Prop) : (term593 _110799 y s) = (@IN _110799 y s).
Proof. exact (@lem4812490 (@IN _110799 y s)). Qed.
Lemma lem4812492 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : @IN _110799 y s.
Proof. exact (EQ_MP (@lem4812491 _110799 y s) (@lem4812488 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4812494 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term155 _110796 _110799 x f y.
Proof. exact (proj1 (@lem4811858 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4812495 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term594 _110796 _110799 x f y.
Proof. exact (fun h0 : (f x) = (f y) => @lem4812494 _110796 _110799 s r x f y h1). Qed.
Lemma lem4812497 (p : Prop) : (term595 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4812498 {_110796 _110799 : Type'} (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term594 _110796 _110799 x f y) = (term155 _110796 _110799 x f y).
Proof. exact (@lem4812497 ((f x) = (f y))). Qed.
Lemma lem4812499 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term155 _110796 _110799 x f y.
Proof. exact (EQ_MP (@lem4812498 _110796 _110799 x f y) (@lem4812495 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4812517 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812518 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term596 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term597 _110796 _110799 f _59650 _59651 s r _59648 _59649).
Proof. exact (@lem4812517 (term558 _110796 _110799 _59649 f _59651) (term559 _110799 _59650 s) (term598 _110796 _110799 _59651 s r _59648 _59649)). Qed.
Lemma lem4812544 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812545 {_110796 _110799 : Type'} (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term598 _110796 _110799 _59651 s r _59648 _59649) = (term599 _110796 _110799 _59651 s r _59648 _59649).
Proof. exact (@lem4812544 (_59648 = _59649) (term559 _110799 _59651 s) (r _59648 _59649)). Qed.
Lemma lem4812561 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4812562 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (_59651 : _110799) (s : _110799 -> Prop) : (term600 _110796 _110799 _59651 s r _59648 _59649) = (term601 _110796 _110799 r _59648 _59649 _59651 s).
Proof. exact (@lem4812561 (r _59648 _59649) (term559 _110799 _59651 s)). Qed.
Lemma lem4812568 {_110796 : Type'} (_59648 : _110796) (_59649 : _110796) : (term602 _110796 _59648 _59649) = (term602 _110796 _59648 _59649).
Proof. exact (eq_refl (term602 _110796 _59648 _59649)). Qed.
Lemma lem4812569 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (_59651 : _110799) (s : _110799 -> Prop) : (term599 _110796 _110799 _59651 s r _59648 _59649) = (term603 _110796 _110799 r _59648 _59649 _59651 s).
Proof. exact (MK_COMB (@lem4812568 _110796 _59648 _59649) (@lem4812562 _110796 _110799 r _59648 _59649 _59651 s)). Qed.
Lemma lem4812573 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812574 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (_59651 : _110799) (s : _110799 -> Prop) : (term603 _110796 _110799 r _59648 _59649 _59651 s) = (term604 _110796 _110799 r _59648 _59649 _59651 s).
Proof. exact (@lem4812573 (r _59648 _59649) (_59648 = _59649) (term559 _110799 _59651 s)). Qed.
Lemma lem4812592 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (_59651 : _110799) (s : _110799 -> Prop) : (term599 _110796 _110799 _59651 s r _59648 _59649) = (term604 _110796 _110799 r _59648 _59649 _59651 s).
Proof. exact (TRANS (@lem4812569 _110796 _110799 r _59648 _59649 _59651 s) (@lem4812574 _110796 _110799 r _59648 _59649 _59651 s)). Qed.
Lemma lem4812593 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (_59651 : _110799) (s : _110799 -> Prop) : (term598 _110796 _110799 _59651 s r _59648 _59649) = (term604 _110796 _110799 r _59648 _59649 _59651 s).
Proof. exact (TRANS (@lem4812545 _110796 _110799 _59651 s r _59648 _59649) (@lem4812592 _110796 _110799 r _59648 _59649 _59651 s)). Qed.
Lemma lem4812594 {_110799 : Type'} (_59650 : _110799) (s : _110799 -> Prop) : (term143 _110799 _59650 s) = (term143 _110799 _59650 s).
Proof. exact (eq_refl (term143 _110799 _59650 s)). Qed.
Lemma lem4812595 {_110796 _110799 : Type'} (_59650 : _110799) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (_59651 : _110799) (s : _110799 -> Prop) : (term605 _110796 _110799 _59650 _59651 s r _59648 _59649) = (term606 _110796 _110799 _59650 r _59648 _59649 _59651 s).
Proof. exact (MK_COMB (@lem4812594 _110799 _59650 s) (@lem4812593 _110796 _110799 r _59648 _59649 _59651 s)). Qed.
Lemma lem4812599 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812600 {_110796 _110799 : Type'} (r : type1402 _110796) (_59650 : _110799) (_59648 : _110796) (_59649 : _110796) (_59651 : _110799) (s : _110799 -> Prop) : (term606 _110796 _110799 _59650 r _59648 _59649 _59651 s) = (term607 _110796 _110799 r _59650 _59648 _59649 _59651 s).
Proof. exact (@lem4812599 (r _59648 _59649) (term559 _110799 _59650 s) (term608 _110796 _110799 _59648 _59649 _59651 s)). Qed.
Lemma lem4812614 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812615 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term609 _110796 _110799 _59650 _59648 _59649 _59651 s) = (term610 _110796 _110799 _59648 _59649 _59650 _59651 s).
Proof. exact (@lem4812614 (_59648 = _59649) (term559 _110799 _59650 s) (term559 _110799 _59651 s)). Qed.
Lemma lem4812633 {_110796 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term611 _110796 r _59648 _59649) = (term611 _110796 r _59648 _59649).
Proof. exact (eq_refl (term611 _110796 r _59648 _59649)). Qed.
Lemma lem4812634 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term607 _110796 _110799 r _59650 _59648 _59649 _59651 s) = (term612 _110796 _110799 r _59648 _59649 _59650 _59651 s).
Proof. exact (MK_COMB (@lem4812633 _110796 r _59648 _59649) (@lem4812615 _110796 _110799 _59648 _59649 _59650 _59651 s)). Qed.
Lemma lem4812645 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term606 _110796 _110799 _59650 r _59648 _59649 _59651 s) = (term612 _110796 _110799 r _59648 _59649 _59650 _59651 s).
Proof. exact (TRANS (@lem4812600 _110796 _110799 r _59650 _59648 _59649 _59651 s) (@lem4812634 _110796 _110799 r _59648 _59649 _59650 _59651 s)). Qed.
Lemma lem4812646 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term605 _110796 _110799 _59650 _59651 s r _59648 _59649) = (term612 _110796 _110799 r _59648 _59649 _59650 _59651 s).
Proof. exact (TRANS (@lem4812595 _110796 _110799 _59650 r _59648 _59649 _59651 s) (@lem4812645 _110796 _110799 r _59648 _59649 _59650 _59651 s)). Qed.
Lemma lem4812647 {_110796 _110799 : Type'} (_59649 : _110796) (f : _110799 -> _110796) (_59651 : _110799) : (term613 _110796 _110799 _59649 f _59651) = (term613 _110796 _110799 _59649 f _59651).
Proof. exact (eq_refl (term613 _110796 _110799 _59649 f _59651)). Qed.
Lemma lem4812648 {_110796 _110799 : Type'} (f : _110799 -> _110796) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term597 _110796 _110799 f _59650 _59651 s r _59648 _59649) = (term614 _110796 _110799 f r _59648 _59649 _59650 _59651 s).
Proof. exact (MK_COMB (@lem4812647 _110796 _110799 _59649 f _59651) (@lem4812646 _110796 _110799 r _59648 _59649 _59650 _59651 s)). Qed.
Lemma lem4812652 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812653 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59648 : _110796) (_59649 : _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term614 _110796 _110799 f r _59648 _59649 _59650 _59651 s) = (term615 _110796 _110799 r f _59648 _59649 _59650 _59651 s).
Proof. exact (@lem4812652 (r _59648 _59649) (term558 _110796 _110799 _59649 f _59651) (term610 _110796 _110799 _59648 _59649 _59650 _59651 s)). Qed.
Lemma lem4812667 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812668 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term616 _110796 _110799 f _59648 _59649 _59650 _59651 s) = (term617 _110796 _110799 _59648 _59649 f _59650 _59651 s).
Proof. exact (@lem4812667 (_59648 = _59649) (term558 _110796 _110799 _59649 f _59651) (term618 _110799 _59650 _59651 s)). Qed.
Lemma lem4812698 {_110796 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term611 _110796 r _59648 _59649) = (term611 _110796 r _59648 _59649).
Proof. exact (eq_refl (term611 _110796 r _59648 _59649)). Qed.
Lemma lem4812699 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term615 _110796 _110799 r f _59648 _59649 _59650 _59651 s) = (term619 _110796 _110799 r _59648 _59649 f _59650 _59651 s).
Proof. exact (MK_COMB (@lem4812698 _110796 r _59648 _59649) (@lem4812668 _110796 _110799 _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812710 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term614 _110796 _110799 f r _59648 _59649 _59650 _59651 s) = (term619 _110796 _110799 r _59648 _59649 f _59650 _59651 s).
Proof. exact (TRANS (@lem4812653 _110796 _110799 r f _59648 _59649 _59650 _59651 s) (@lem4812699 _110796 _110799 r _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812711 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term597 _110796 _110799 f _59650 _59651 s r _59648 _59649) = (term619 _110796 _110799 r _59648 _59649 f _59650 _59651 s).
Proof. exact (TRANS (@lem4812648 _110796 _110799 f r _59648 _59649 _59650 _59651 s) (@lem4812710 _110796 _110799 r _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812712 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term596 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term619 _110796 _110799 r _59648 _59649 f _59650 _59651 s).
Proof. exact (TRANS (@lem4812518 _110796 _110799 f _59650 _59651 s r _59648 _59649) (@lem4812711 _110796 _110799 r _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812713 {_110796 _110799 : Type'} (_59648 : _110796) (f : _110799 -> _110796) (_59650 : _110799) : (term613 _110796 _110799 _59648 f _59650) = (term613 _110796 _110799 _59648 f _59650).
Proof. exact (eq_refl (term613 _110796 _110799 _59648 f _59650)). Qed.
Lemma lem4812714 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term562 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term620 _110796 _110799 r _59648 _59649 f _59650 _59651 s).
Proof. exact (MK_COMB (@lem4812713 _110796 _110799 _59648 f _59650) (@lem4812712 _110796 _110799 r _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812718 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812719 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term620 _110796 _110799 r _59648 _59649 f _59650 _59651 s) = (term621 _110796 _110799 r _59648 _59649 f _59650 _59651 s).
Proof. exact (@lem4812718 (r _59648 _59649) (term558 _110796 _110799 _59648 f _59650) (term617 _110796 _110799 _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812733 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812734 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term622 _110796 _110799 _59648 _59649 f _59650 _59651 s) = (term623 _110796 _110799 _59648 _59649 f _59650 _59651 s).
Proof. exact (@lem4812733 (_59648 = _59649) (term558 _110796 _110799 _59648 f _59650) (term624 _110796 _110799 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812776 {_110796 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term611 _110796 r _59648 _59649) = (term611 _110796 r _59648 _59649).
Proof. exact (eq_refl (term611 _110796 r _59648 _59649)). Qed.
Lemma lem4812777 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term621 _110796 _110799 r _59648 _59649 f _59650 _59651 s) = (term625 _110796 _110799 r _59648 _59649 f _59650 _59651 s).
Proof. exact (MK_COMB (@lem4812776 _110796 r _59648 _59649) (@lem4812734 _110796 _110799 _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812788 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term620 _110796 _110799 r _59648 _59649 f _59650 _59651 s) = (term625 _110796 _110799 r _59648 _59649 f _59650 _59651 s).
Proof. exact (TRANS (@lem4812719 _110796 _110799 r _59648 _59649 f _59650 _59651 s) (@lem4812777 _110796 _110799 r _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812789 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term562 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term625 _110796 _110799 r _59648 _59649 f _59650 _59651 s).
Proof. exact (TRANS (@lem4812714 _110796 _110799 r _59648 _59649 f _59650 _59651 s) (@lem4812788 _110796 _110799 r _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4812791 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term626 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term627 _110796 _110799 r _59648 _59649 f _59650 _59651 s).
Proof. exact (MK_COMB (@lem4812790) (@lem4812789 _110796 _110799 r _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812817 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812818 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term628 _110796 _110799 _59650 f _59651 s _59648 _59649) = (term629 _110796 _110799 f _59650 _59651 s _59648 _59649).
Proof. exact (@lem4812817 (term558 _110796 _110799 _59649 f _59651) (term559 _110799 _59650 s) (term630 _110796 _110799 _59651 s _59648 _59649)). Qed.
Lemma lem4812844 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4812845 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (_59651 : _110799) (s : _110799 -> Prop) : (term630 _110796 _110799 _59651 s _59648 _59649) = (term608 _110796 _110799 _59648 _59649 _59651 s).
Proof. exact (@lem4812844 (_59648 = _59649) (term559 _110799 _59651 s)). Qed.
Lemma lem4812853 {_110799 : Type'} (_59650 : _110799) (s : _110799 -> Prop) : (term143 _110799 _59650 s) = (term143 _110799 _59650 s).
Proof. exact (eq_refl (term143 _110799 _59650 s)). Qed.
Lemma lem4812854 {_110796 _110799 : Type'} (_59650 : _110799) (_59648 : _110796) (_59649 : _110796) (_59651 : _110799) (s : _110799 -> Prop) : (term631 _110796 _110799 _59650 _59651 s _59648 _59649) = (term609 _110796 _110799 _59650 _59648 _59649 _59651 s).
Proof. exact (MK_COMB (@lem4812853 _110799 _59650 s) (@lem4812845 _110796 _110799 _59648 _59649 _59651 s)). Qed.
Lemma lem4812858 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812859 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term609 _110796 _110799 _59650 _59648 _59649 _59651 s) = (term610 _110796 _110799 _59648 _59649 _59650 _59651 s).
Proof. exact (@lem4812858 (_59648 = _59649) (term559 _110799 _59650 s) (term559 _110799 _59651 s)). Qed.
Lemma lem4812877 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term631 _110796 _110799 _59650 _59651 s _59648 _59649) = (term610 _110796 _110799 _59648 _59649 _59650 _59651 s).
Proof. exact (TRANS (@lem4812854 _110796 _110799 _59650 _59648 _59649 _59651 s) (@lem4812859 _110796 _110799 _59648 _59649 _59650 _59651 s)). Qed.
Lemma lem4812878 {_110796 _110799 : Type'} (_59649 : _110796) (f : _110799 -> _110796) (_59651 : _110799) : (term613 _110796 _110799 _59649 f _59651) = (term613 _110796 _110799 _59649 f _59651).
Proof. exact (eq_refl (term613 _110796 _110799 _59649 f _59651)). Qed.
Lemma lem4812879 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59648 : _110796) (_59649 : _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term629 _110796 _110799 f _59650 _59651 s _59648 _59649) = (term616 _110796 _110799 f _59648 _59649 _59650 _59651 s).
Proof. exact (MK_COMB (@lem4812878 _110796 _110799 _59649 f _59651) (@lem4812877 _110796 _110799 _59648 _59649 _59650 _59651 s)). Qed.
Lemma lem4812883 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812884 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term616 _110796 _110799 f _59648 _59649 _59650 _59651 s) = (term617 _110796 _110799 _59648 _59649 f _59650 _59651 s).
Proof. exact (@lem4812883 (_59648 = _59649) (term558 _110796 _110799 _59649 f _59651) (term618 _110799 _59650 _59651 s)). Qed.
Lemma lem4812914 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term629 _110796 _110799 f _59650 _59651 s _59648 _59649) = (term617 _110796 _110799 _59648 _59649 f _59650 _59651 s).
Proof. exact (TRANS (@lem4812879 _110796 _110799 f _59648 _59649 _59650 _59651 s) (@lem4812884 _110796 _110799 _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812915 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term628 _110796 _110799 _59650 f _59651 s _59648 _59649) = (term617 _110796 _110799 _59648 _59649 f _59650 _59651 s).
Proof. exact (TRANS (@lem4812818 _110796 _110799 f _59650 _59651 s _59648 _59649) (@lem4812914 _110796 _110799 _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812916 {_110796 _110799 : Type'} (_59648 : _110796) (f : _110799 -> _110796) (_59650 : _110799) : (term613 _110796 _110799 _59648 f _59650) = (term613 _110796 _110799 _59648 f _59650).
Proof. exact (eq_refl (term613 _110796 _110799 _59648 f _59650)). Qed.
Lemma lem4812917 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term632 _110796 _110799 _59650 f _59651 s _59648 _59649) = (term622 _110796 _110799 _59648 _59649 f _59650 _59651 s).
Proof. exact (MK_COMB (@lem4812916 _110796 _110799 _59648 f _59650) (@lem4812915 _110796 _110799 _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812921 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4812922 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term622 _110796 _110799 _59648 _59649 f _59650 _59651 s) = (term623 _110796 _110799 _59648 _59649 f _59650 _59651 s).
Proof. exact (@lem4812921 (_59648 = _59649) (term558 _110796 _110799 _59648 f _59650) (term624 _110796 _110799 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812964 {_110796 _110799 : Type'} (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term632 _110796 _110799 _59650 f _59651 s _59648 _59649) = (term623 _110796 _110799 _59648 _59649 f _59650 _59651 s).
Proof. exact (TRANS (@lem4812917 _110796 _110799 _59648 _59649 f _59650 _59651 s) (@lem4812922 _110796 _110799 _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812965 {_110796 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term611 _110796 r _59648 _59649) = (term611 _110796 r _59648 _59649).
Proof. exact (eq_refl (term611 _110796 r _59648 _59649)). Qed.
Lemma lem4812966 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : (term633 _110796 _110799 r _59650 f _59651 s _59648 _59649) = (term625 _110796 _110799 r _59648 _59649 f _59650 _59651 s).
Proof. exact (MK_COMB (@lem4812965 _110796 r _59648 _59649) (@lem4812964 _110796 _110799 _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812977 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : ((term562 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term633 _110796 _110799 r _59650 f _59651 s _59648 _59649)) = ((term625 _110796 _110799 r _59648 _59649 f _59650 _59651 s) = (term625 _110796 _110799 r _59648 _59649 f _59650 _59651 s)).
Proof. exact (MK_COMB (@lem4812791 _110796 _110799 r _59648 _59649 f _59650 _59651 s) (@lem4812966 _110796 _110799 r _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812979 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4812980 (x : Prop) : (x = x) = True.
Proof. exact (@lem4812979 Prop x). Qed.
Lemma lem4812981 {_110796 _110799 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) (f : _110799 -> _110796) (_59650 : _110799) (_59651 : _110799) (s : _110799 -> Prop) : ((term625 _110796 _110799 r _59648 _59649 f _59650 _59651 s) = (term625 _110796 _110799 r _59648 _59649 f _59650 _59651 s)) = True.
Proof. exact (@lem4812980 (term625 _110796 _110799 r _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812982 {_110796 _110799 : Type'} (r : type1402 _110796) (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : ((term562 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term633 _110796 _110799 r _59650 f _59651 s _59648 _59649)) = True.
Proof. exact (TRANS (@lem4812977 _110796 _110799 r _59648 _59649 f _59650 _59651 s) (@lem4812981 _110796 _110799 r _59648 _59649 f _59650 _59651 s)). Qed.
Lemma lem4812983 {_110796 _110799 : Type'} (r : type1402 _110796) (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : True = ((term562 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term633 _110796 _110799 r _59650 f _59651 s _59648 _59649)).
Proof. exact (SYM (@lem4812982 _110796 _110799 r _59650 f _59651 s _59648 _59649)). Qed.
Lemma lem4812984 {_110796 _110799 : Type'} (r : type1402 _110796) (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term562 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term633 _110796 _110799 r _59650 f _59651 s _59648 _59649).
Proof. exact (EQ_MP (@lem4812983 _110796 _110799 r _59650 f _59651 s _59648 _59649) (@lem0)). Qed.
Lemma lem4812985 {_110796 _110799 : Type'} (_59650 : _110799) (_59651 : _110799) (_59648 : _110796) (_59649 : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term633 _110796 _110799 r _59650 f _59651 s _59648 _59649.
Proof. exact (EQ_MP (@lem4812984 _110796 _110799 r _59650 f _59651 s _59648 _59649) (@lem4812186 _110796 _110799 _59650 _59651 _59648 _59649 s r x f y h1)). Qed.
Lemma lem4812987 (b : Prop) (a : Prop) : (a \/ b) = (term634 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4812988 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term633 _110796 _110799 r _59650 f _59651 s _59648 _59649) = (term635 _110796 _110799 _59650 f _59651 s r _59648 _59649).
Proof. exact (@lem4812987 (term632 _110796 _110799 _59650 f _59651 s _59648 _59649) (r _59648 _59649)). Qed.
Lemma lem4812990 (a : Prop) (b : Prop) : (term636 a b) = (term637 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4812991 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term638 _110796 _110799 _59650 f _59651 s _59648 _59649) = (term639 _110796 _110799 _59650 f _59651 s _59648 _59649).
Proof. exact (@lem4812990 (term558 _110796 _110799 _59648 f _59650) (term628 _110796 _110799 _59650 f _59651 s _59648 _59649)). Qed.
Lemma lem4812993 (a : Prop) : (term86 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4812994 {_110796 _110799 : Type'} (_59648 : _110796) (f : _110799 -> _110796) (_59650 : _110799) : (term640 _110796 _110799 _59648 f _59650) = (_59648 = (f _59650)).
Proof. exact (@lem4812993 (_59648 = (f _59650))). Qed.
Lemma lem4812995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4812996 {_110796 _110799 : Type'} (_59648 : _110796) (f : _110799 -> _110796) (_59650 : _110799) : (term641 _110796 _110799 _59648 f _59650) = (term642 _110796 _110799 _59648 f _59650).
Proof. exact (MK_COMB (@lem4812995) (@lem4812994 _110796 _110799 _59648 f _59650)). Qed.
Lemma lem4812998 (a : Prop) (b : Prop) : (term636 a b) = (term637 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4812999 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term643 _110796 _110799 _59650 f _59651 s _59648 _59649) = (term644 _110796 _110799 _59650 f _59651 s _59648 _59649).
Proof. exact (@lem4812998 (term559 _110799 _59650 s) (term645 _110796 _110799 f _59651 s _59648 _59649)). Qed.
Lemma lem4813001 (a : Prop) : (term86 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4813002 {_110799 : Type'} (_59650 : _110799) (s : _110799 -> Prop) : (term646 _110799 _59650 s) = (@IN _110799 _59650 s).
Proof. exact (@lem4813001 (@IN _110799 _59650 s)). Qed.
Lemma lem4813003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4813004 {_110799 : Type'} (_59650 : _110799) (s : _110799 -> Prop) : (term647 _110799 _59650 s) = (term648 _110799 _59650 s).
Proof. exact (MK_COMB (@lem4813003) (@lem4813002 _110799 _59650 s)). Qed.
Lemma lem4813006 (a : Prop) (b : Prop) : (term636 a b) = (term637 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4813007 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term649 _110796 _110799 f _59651 s _59648 _59649) = (term650 _110796 _110799 f _59651 s _59648 _59649).
Proof. exact (@lem4813006 (term558 _110796 _110799 _59649 f _59651) (term630 _110796 _110799 _59651 s _59648 _59649)). Qed.
Lemma lem4813009 (a : Prop) : (term86 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4813010 {_110796 _110799 : Type'} (_59649 : _110796) (f : _110799 -> _110796) (_59651 : _110799) : (term640 _110796 _110799 _59649 f _59651) = (_59649 = (f _59651)).
Proof. exact (@lem4813009 (_59649 = (f _59651))). Qed.
Lemma lem4813011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4813012 {_110796 _110799 : Type'} (_59649 : _110796) (f : _110799 -> _110796) (_59651 : _110799) : (term641 _110796 _110799 _59649 f _59651) = (term642 _110796 _110799 _59649 f _59651).
Proof. exact (MK_COMB (@lem4813011) (@lem4813010 _110796 _110799 _59649 f _59651)). Qed.
Lemma lem4813014 (a : Prop) (b : Prop) : (term636 a b) = (term637 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4813015 {_110796 _110799 : Type'} (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term651 _110796 _110799 _59651 s _59648 _59649) = (term652 _110796 _110799 _59651 s _59648 _59649).
Proof. exact (@lem4813014 (term559 _110799 _59651 s) (_59648 = _59649)). Qed.
Lemma lem4813017 (a : Prop) : (term86 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4813018 {_110799 : Type'} (_59651 : _110799) (s : _110799 -> Prop) : (term646 _110799 _59651 s) = (@IN _110799 _59651 s).
Proof. exact (@lem4813017 (@IN _110799 _59651 s)). Qed.
Lemma lem4813019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4813020 {_110799 : Type'} (_59651 : _110799) (s : _110799 -> Prop) : (term647 _110799 _59651 s) = (term648 _110799 _59651 s).
Proof. exact (MK_COMB (@lem4813019) (@lem4813018 _110799 _59651 s)). Qed.
Lemma lem4813021 {_110796 : Type'} (_59648 : _110796) (_59649 : _110796) : (term24 _110796 _59648 _59649) = (term24 _110796 _59648 _59649).
Proof. exact (eq_refl (term24 _110796 _59648 _59649)). Qed.
Lemma lem4813022 {_110796 _110799 : Type'} (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term652 _110796 _110799 _59651 s _59648 _59649) = (term653 _110796 _110799 _59651 s _59648 _59649).
Proof. exact (MK_COMB (@lem4813020 _110799 _59651 s) (@lem4813021 _110796 _59648 _59649)). Qed.
Lemma lem4813023 {_110796 _110799 : Type'} (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term651 _110796 _110799 _59651 s _59648 _59649) = (term653 _110796 _110799 _59651 s _59648 _59649).
Proof. exact (TRANS (@lem4813015 _110796 _110799 _59651 s _59648 _59649) (@lem4813022 _110796 _110799 _59651 s _59648 _59649)). Qed.
Lemma lem4813024 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term650 _110796 _110799 f _59651 s _59648 _59649) = (term654 _110796 _110799 f _59651 s _59648 _59649).
Proof. exact (MK_COMB (@lem4813012 _110796 _110799 _59649 f _59651) (@lem4813023 _110796 _110799 _59651 s _59648 _59649)). Qed.
Lemma lem4813025 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term649 _110796 _110799 f _59651 s _59648 _59649) = (term654 _110796 _110799 f _59651 s _59648 _59649).
Proof. exact (TRANS (@lem4813007 _110796 _110799 f _59651 s _59648 _59649) (@lem4813024 _110796 _110799 f _59651 s _59648 _59649)). Qed.
Lemma lem4813026 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term644 _110796 _110799 _59650 f _59651 s _59648 _59649) = (term655 _110796 _110799 _59650 f _59651 s _59648 _59649).
Proof. exact (MK_COMB (@lem4813004 _110799 _59650 s) (@lem4813025 _110796 _110799 f _59651 s _59648 _59649)). Qed.
Lemma lem4813027 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term643 _110796 _110799 _59650 f _59651 s _59648 _59649) = (term655 _110796 _110799 _59650 f _59651 s _59648 _59649).
Proof. exact (TRANS (@lem4812999 _110796 _110799 _59650 f _59651 s _59648 _59649) (@lem4813026 _110796 _110799 _59650 f _59651 s _59648 _59649)). Qed.
Lemma lem4813028 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term639 _110796 _110799 _59650 f _59651 s _59648 _59649) = (term656 _110796 _110799 _59650 f _59651 s _59648 _59649).
Proof. exact (MK_COMB (@lem4812996 _110796 _110799 _59648 f _59650) (@lem4813027 _110796 _110799 _59650 f _59651 s _59648 _59649)). Qed.
Lemma lem4813029 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term638 _110796 _110799 _59650 f _59651 s _59648 _59649) = (term656 _110796 _110799 _59650 f _59651 s _59648 _59649).
Proof. exact (TRANS (@lem4812991 _110796 _110799 _59650 f _59651 s _59648 _59649) (@lem4813028 _110796 _110799 _59650 f _59651 s _59648 _59649)). Qed.
Lemma lem4813030 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4813031 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (_59648 : _110796) (_59649 : _110796) : (term657 _110796 _110799 _59650 f _59651 s _59648 _59649) = (term658 _110796 _110799 _59650 f _59651 s _59648 _59649).
Proof. exact (MK_COMB (@lem4813030) (@lem4813029 _110796 _110799 _59650 f _59651 s _59648 _59649)). Qed.
Lemma lem4813032 {_110796 : Type'} (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (r _59648 _59649) = (r _59648 _59649).
Proof. exact (eq_refl (r _59648 _59649)). Qed.
Lemma lem4813033 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term635 _110796 _110799 _59650 f _59651 s r _59648 _59649) = (term659 _110796 _110799 _59650 f _59651 s r _59648 _59649).
Proof. exact (MK_COMB (@lem4813031 _110796 _110799 _59650 f _59651 s _59648 _59649) (@lem4813032 _110796 r _59648 _59649)). Qed.
Lemma lem4813034 {_110796 _110799 : Type'} (_59650 : _110799) (f : _110799 -> _110796) (_59651 : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (_59648 : _110796) (_59649 : _110796) : (term633 _110796 _110799 r _59650 f _59651 s _59648 _59649) = (term659 _110796 _110799 _59650 f _59651 s r _59648 _59649).
Proof. exact (TRANS (@lem4812988 _110796 _110799 _59650 f _59651 s r _59648 _59649) (@lem4813033 _110796 _110799 _59650 f _59651 s r _59648 _59649)). Qed.
Lemma lem4813036 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term660 _110796 _110799 s x f y.
Proof. exact (conj (@lem4812492 _110796 _110799 s r x f y h1) (@lem4812499 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4813037 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term661 _110796 _110799 s x f y.
Proof. exact (conj (@lem4812485 _110796 _110799 f y) (@lem4813036 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4813038 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term662 _110796 _110799 s x f y.
Proof. exact (conj (@lem4812476 _110796 _110799 s r x f y h1) (@lem4813037 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4813039 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term663 _110796 _110799 s x f y.
Proof. exact (conj (@lem4812469 _110796 _110799 f x) (@lem4813038 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4813041 {_110796 _110799 : Type'} (_59650 : _110799) (_59651 : _110799) (_59648 : _110796) (_59649 : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term659 _110796 _110799 _59650 f _59651 s r _59648 _59649.
Proof. exact (EQ_MP (@lem4813034 _110796 _110799 _59650 f _59651 s r _59648 _59649) (@lem4812985 _110796 _110799 _59650 _59651 _59648 _59649 s r x f y h1)). Qed.
Lemma lem4813042 {_110796 _110799 : Type'} (_59650 : _110799) (_59651 : _110799) (_59648 : _110796) (_59649 : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term659 _110796 _110799 _59650 f _59651 s r _59648 _59649.
Proof. exact (@lem4813041 _110796 _110799 _59650 _59651 _59648 _59649 s r x f y h1). Qed.
Lemma lem4813043 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term664 _110796 _110799 s r x f y.
Proof. exact (@lem4813042 _110796 _110799 x y (f x) (f y) s r x f y h1). Qed.
Lemma lem4813046 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term152 _110796 _110799 r x f y.
Proof. exact (@lem4813043 _110796 _110799 s r x f y h1 (@lem4813039 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4813047 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term665 _110796 _110799 r x f y.
Proof. exact (fun h0 : term563 _110796 _110799 r x f y => @lem4813046 _110796 _110799 s r x f y h1). Qed.
Lemma lem4813049 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4813050 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term665 _110796 _110799 r x f y) = (term152 _110796 _110799 r x f y).
Proof. exact (@lem4813049 (term152 _110796 _110799 r x f y)). Qed.
Lemma lem4813051 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term152 _110796 _110799 r x f y.
Proof. exact (EQ_MP (@lem4813050 _110796 _110799 r x f y) (@lem4813047 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4813054 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4813056 {_110796 _110799 : Type'} (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) : (term563 _110796 _110799 r x f y) = (term666 _110796 _110799 r x f y).
Proof. exact (@lem4813054 (term152 _110796 _110799 r x f y)). Qed.
Lemma lem4813059 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term666 _110796 _110799 r x f y.
Proof. exact (EQ_MP (@lem4813056 _110796 _110799 r x f y) (@lem4812190 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4813062 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : False.
Proof. exact (@lem4813059 _110796 _110799 s r x f y h1 (@lem4813051 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4813063 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : term667.
Proof. exact (fun h0 : ~ False => @lem4813062 _110796 _110799 s r x f y h1). Qed.
Lemma lem4813065 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4813066 : term667 = False.
Proof. exact (@lem4813065 False). Qed.
Lemma lem4813067 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (x : _110799) (f : _110799 -> _110796) (y : _110799) (h1 : term221 _110796 _110799 s r x f y) : False.
Proof. exact (EQ_MP (@lem4813066) (@lem4813063 _110796 _110799 s r x f y h1)). Qed.
Lemma lem4813106 {_110796 _110799 : Type'} (f : _110799 -> _110796) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4813107 {_110799 : Type'} (_59698 : _110799) (_59699 : _110799) (h1 : _59698 = _59699) : _59698 = _59699.
Proof. exact (h1). Qed.
Lemma lem4813108 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59698 : _110799) (_59699 : _110799) (h1 : _59698 = _59699) : (f _59698) = (f _59699).
Proof. exact (MK_COMB (@lem4813106 _110796 _110799 f) (@lem4813107 _110799 _59698 _59699 h1)). Qed.
Lemma lem4813109 {_110796 _110799 : Type'} (_59698 : _110799) (f : _110799 -> _110796) (_59699 : _110799) : term668 _110796 _110799 _59698 f _59699.
Proof. exact (fun h0 : _59698 = _59699 => @lem4813108 _110796 _110799 f _59698 _59699 h0). Qed.
Lemma lem4813111 (a : Prop) (b : Prop) : (a -> b) = (term669 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4813112 {_110796 _110799 : Type'} (_59698 : _110799) (f : _110799 -> _110796) (_59699 : _110799) : (term668 _110796 _110799 _59698 f _59699) = (term670 _110796 _110799 _59698 f _59699).
Proof. exact (@lem4813111 (_59698 = _59699) ((f _59698) = (f _59699))). Qed.
Lemma lem4813113 {_110796 _110799 : Type'} (_59698 : _110799) (f : _110799 -> _110796) (_59699 : _110799) : term670 _110796 _110799 _59698 f _59699.
Proof. exact (EQ_MP (@lem4813112 _110796 _110799 _59698 f _59699) (@lem4813109 _110796 _110799 _59698 f _59699)). Qed.
Lemma lem4813121 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : @IN _110799 x'' s.
Proof. exact (proj2 (@lem4811871 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813122 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term593 _110799 x'' s.
Proof. exact (fun h0 : term559 _110799 x'' s => @lem4813121 _110796 _110799 x'' x''' x' y' s r f h1). Qed.
Lemma lem4813124 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4813125 {_110799 : Type'} (x'' : _110799) (s : _110799 -> Prop) : (term593 _110799 x'' s) = (@IN _110799 x'' s).
Proof. exact (@lem4813124 (@IN _110799 x'' s)). Qed.
Lemma lem4813126 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : @IN _110799 x'' s.
Proof. exact (EQ_MP (@lem4813125 _110799 x'' s) (@lem4813122 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813128 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : @IN _110799 x''' s.
Proof. exact (proj2 (@lem4811873 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813129 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term593 _110799 x''' s.
Proof. exact (fun h0 : term559 _110799 x''' s => @lem4813128 _110796 _110799 x'' x''' x' y' s r f h1). Qed.
Lemma lem4813131 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4813132 {_110799 : Type'} (x''' : _110799) (s : _110799 -> Prop) : (term593 _110799 x''' s) = (@IN _110799 x''' s).
Proof. exact (@lem4813131 (@IN _110799 x''' s)). Qed.
Lemma lem4813133 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : @IN _110799 x''' s.
Proof. exact (EQ_MP (@lem4813132 _110799 x''' s) (@lem4813129 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813136 {_110796 _110799 : Type'} (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) (h1 : term155 _110796 _110799 x'' f x''') : term155 _110796 _110799 x'' f x'''.
Proof. exact (h1). Qed.
Lemma lem4813137 {_110796 _110799 : Type'} (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) (h1 : term155 _110796 _110799 x'' f x''') : term594 _110796 _110799 x'' f x'''.
Proof. exact (fun h0 : (f x'') = (f x''') => @lem4813136 _110796 _110799 x'' f x''' h1). Qed.
Lemma lem4813139 (p : Prop) : (term595 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4813140 {_110796 _110799 : Type'} (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : (term594 _110796 _110799 x'' f x''') = (term155 _110796 _110799 x'' f x''').
Proof. exact (@lem4813139 ((f x'') = (f x'''))). Qed.
Lemma lem4813141 {_110796 _110799 : Type'} (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) (h1 : term155 _110796 _110799 x'' f x''') : term155 _110796 _110799 x'' f x'''.
Proof. exact (EQ_MP (@lem4813140 _110796 _110799 x'' f x''') (@lem4813137 _110796 _110799 x'' f x''' h1)). Qed.
Lemma lem4813143 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term563 _110796 _110799 r x'' f x'''.
Proof. exact (EQ_MP (@lem4812366 _110796 _110799 x'' x''' x' y' s r f h1) (@lem4812271 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813144 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term671 _110796 _110799 r x'' f x'''.
Proof. exact (fun h0 : term152 _110796 _110799 r x'' f x''' => @lem4813143 _110796 _110799 x'' x''' x' y' s r f h1). Qed.
Lemma lem4813146 (p : Prop) : (term595 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4813147 {_110796 _110799 : Type'} (r : type1402 _110796) (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : (term671 _110796 _110799 r x'' f x''') = (term563 _110796 _110799 r x'' f x''').
Proof. exact (@lem4813146 (term152 _110796 _110799 r x'' f x''')). Qed.
Lemma lem4813148 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term563 _110796 _110799 r x'' f x'''.
Proof. exact (EQ_MP (@lem4813147 _110796 _110799 r x'' f x''') (@lem4813144 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813164 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813165 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term566 _110796 _110799 s r _59652 f _59653) = (term672 _110796 _110799 s r _59652 f _59653).
Proof. exact (@lem4813164 (_59652 = _59653) (term559 _110799 _59653 s) (term159 _110796 _110799 r _59652 f _59653)). Qed.
Lemma lem4813181 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813182 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term673 _110796 _110799 s r _59652 f _59653) = (term674 _110796 _110799 s r _59652 f _59653).
Proof. exact (@lem4813181 ((f _59652) = (f _59653)) (term559 _110799 _59653 s) (term152 _110796 _110799 r _59652 f _59653)). Qed.
Lemma lem4813198 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4813199 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term675 _110796 _110799 s r _59652 f _59653) = (term676 _110796 _110799 r _59652 f _59653 s).
Proof. exact (@lem4813198 (term152 _110796 _110799 r _59652 f _59653) (term559 _110799 _59653 s)). Qed.
Lemma lem4813205 {_110796 _110799 : Type'} (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term157 _110796 _110799 _59652 f _59653) = (term157 _110796 _110799 _59652 f _59653).
Proof. exact (eq_refl (term157 _110796 _110799 _59652 f _59653)). Qed.
Lemma lem4813206 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term674 _110796 _110799 s r _59652 f _59653) = (term677 _110796 _110799 r _59652 f _59653 s).
Proof. exact (MK_COMB (@lem4813205 _110796 _110799 _59652 f _59653) (@lem4813199 _110796 _110799 r _59652 f _59653 s)). Qed.
Lemma lem4813210 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813211 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term677 _110796 _110799 r _59652 f _59653 s) = (term678 _110796 _110799 r _59652 f _59653 s).
Proof. exact (@lem4813210 (term152 _110796 _110799 r _59652 f _59653) ((f _59652) = (f _59653)) (term559 _110799 _59653 s)). Qed.
Lemma lem4813229 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term674 _110796 _110799 s r _59652 f _59653) = (term678 _110796 _110799 r _59652 f _59653 s).
Proof. exact (TRANS (@lem4813206 _110796 _110799 r _59652 f _59653 s) (@lem4813211 _110796 _110799 r _59652 f _59653 s)). Qed.
Lemma lem4813230 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term673 _110796 _110799 s r _59652 f _59653) = (term678 _110796 _110799 r _59652 f _59653 s).
Proof. exact (TRANS (@lem4813182 _110796 _110799 s r _59652 f _59653) (@lem4813229 _110796 _110799 r _59652 f _59653 s)). Qed.
Lemma lem4813231 {_110799 : Type'} (_59652 : _110799) (_59653 : _110799) : (term602 _110799 _59652 _59653) = (term602 _110799 _59652 _59653).
Proof. exact (eq_refl (term602 _110799 _59652 _59653)). Qed.
Lemma lem4813232 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term672 _110796 _110799 s r _59652 f _59653) = (term679 _110796 _110799 r _59652 f _59653 s).
Proof. exact (MK_COMB (@lem4813231 _110799 _59652 _59653) (@lem4813230 _110796 _110799 r _59652 f _59653 s)). Qed.
Lemma lem4813236 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813237 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term679 _110796 _110799 r _59652 f _59653 s) = (term680 _110796 _110799 r _59652 f _59653 s).
Proof. exact (@lem4813236 (term152 _110796 _110799 r _59652 f _59653) (_59652 = _59653) (term681 _110796 _110799 _59652 f _59653 s)). Qed.
Lemma lem4813251 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813252 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term682 _110796 _110799 _59652 f _59653 s) = (term683 _110796 _110799 f _59652 _59653 s).
Proof. exact (@lem4813251 ((f _59652) = (f _59653)) (_59652 = _59653) (term559 _110799 _59653 s)). Qed.
Lemma lem4813272 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term684 _110796 _110799 r _59652 f _59653) = (term684 _110796 _110799 r _59652 f _59653).
Proof. exact (eq_refl (term684 _110796 _110799 r _59652 f _59653)). Qed.
Lemma lem4813273 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term680 _110796 _110799 r _59652 f _59653 s) = (term685 _110796 _110799 r f _59652 _59653 s).
Proof. exact (MK_COMB (@lem4813272 _110796 _110799 r _59652 f _59653) (@lem4813252 _110796 _110799 f _59652 _59653 s)). Qed.
Lemma lem4813284 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term679 _110796 _110799 r _59652 f _59653 s) = (term685 _110796 _110799 r f _59652 _59653 s).
Proof. exact (TRANS (@lem4813237 _110796 _110799 r _59652 f _59653 s) (@lem4813273 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813285 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term672 _110796 _110799 s r _59652 f _59653) = (term685 _110796 _110799 r f _59652 _59653 s).
Proof. exact (TRANS (@lem4813232 _110796 _110799 r _59652 f _59653 s) (@lem4813284 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813286 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term566 _110796 _110799 s r _59652 f _59653) = (term685 _110796 _110799 r f _59652 _59653 s).
Proof. exact (TRANS (@lem4813165 _110796 _110799 s r _59652 f _59653) (@lem4813285 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813287 {_110799 : Type'} (_59652 : _110799) (s : _110799 -> Prop) : (term143 _110799 _59652 s) = (term143 _110799 _59652 s).
Proof. exact (eq_refl (term143 _110799 _59652 s)). Qed.
Lemma lem4813288 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term567 _110796 _110799 s r _59652 f _59653) = (term686 _110796 _110799 r f _59652 _59653 s).
Proof. exact (MK_COMB (@lem4813287 _110799 _59652 s) (@lem4813286 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813292 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813293 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term686 _110796 _110799 r f _59652 _59653 s) = (term687 _110796 _110799 r f _59652 _59653 s).
Proof. exact (@lem4813292 (term152 _110796 _110799 r _59652 f _59653) (term559 _110799 _59652 s) (term683 _110796 _110799 f _59652 _59653 s)). Qed.
Lemma lem4813307 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813308 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term688 _110796 _110799 f _59652 _59653 s) = (term689 _110796 _110799 f _59652 _59653 s).
Proof. exact (@lem4813307 ((f _59652) = (f _59653)) (term559 _110799 _59652 s) (term690 _110799 _59652 _59653 s)). Qed.
Lemma lem4813324 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813325 {_110799 : Type'} (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term691 _110799 _59652 _59653 s) = (term692 _110799 _59652 _59653 s).
Proof. exact (@lem4813324 (_59652 = _59653) (term559 _110799 _59652 s) (term559 _110799 _59653 s)). Qed.
Lemma lem4813343 {_110796 _110799 : Type'} (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term157 _110796 _110799 _59652 f _59653) = (term157 _110796 _110799 _59652 f _59653).
Proof. exact (eq_refl (term157 _110796 _110799 _59652 f _59653)). Qed.
Lemma lem4813344 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term689 _110796 _110799 f _59652 _59653 s) = (term693 _110796 _110799 f _59652 _59653 s).
Proof. exact (MK_COMB (@lem4813343 _110796 _110799 _59652 f _59653) (@lem4813325 _110799 _59652 _59653 s)). Qed.
Lemma lem4813355 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term688 _110796 _110799 f _59652 _59653 s) = (term693 _110796 _110799 f _59652 _59653 s).
Proof. exact (TRANS (@lem4813308 _110796 _110799 f _59652 _59653 s) (@lem4813344 _110796 _110799 f _59652 _59653 s)). Qed.
Lemma lem4813356 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term684 _110796 _110799 r _59652 f _59653) = (term684 _110796 _110799 r _59652 f _59653).
Proof. exact (eq_refl (term684 _110796 _110799 r _59652 f _59653)). Qed.
Lemma lem4813357 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term687 _110796 _110799 r f _59652 _59653 s) = (term694 _110796 _110799 r f _59652 _59653 s).
Proof. exact (MK_COMB (@lem4813356 _110796 _110799 r _59652 f _59653) (@lem4813355 _110796 _110799 f _59652 _59653 s)). Qed.
Lemma lem4813368 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term686 _110796 _110799 r f _59652 _59653 s) = (term694 _110796 _110799 r f _59652 _59653 s).
Proof. exact (TRANS (@lem4813293 _110796 _110799 r f _59652 _59653 s) (@lem4813357 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813369 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term567 _110796 _110799 s r _59652 f _59653) = (term694 _110796 _110799 r f _59652 _59653 s).
Proof. exact (TRANS (@lem4813288 _110796 _110799 r f _59652 _59653 s) (@lem4813368 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813370 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4813371 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term695 _110796 _110799 s r _59652 f _59653) = (term696 _110796 _110799 r f _59652 _59653 s).
Proof. exact (MK_COMB (@lem4813370) (@lem4813369 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813397 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813398 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term673 _110796 _110799 s r _59652 f _59653) = (term674 _110796 _110799 s r _59652 f _59653).
Proof. exact (@lem4813397 ((f _59652) = (f _59653)) (term559 _110799 _59653 s) (term152 _110796 _110799 r _59652 f _59653)). Qed.
Lemma lem4813414 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4813415 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term675 _110796 _110799 s r _59652 f _59653) = (term676 _110796 _110799 r _59652 f _59653 s).
Proof. exact (@lem4813414 (term152 _110796 _110799 r _59652 f _59653) (term559 _110799 _59653 s)). Qed.
Lemma lem4813421 {_110796 _110799 : Type'} (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term157 _110796 _110799 _59652 f _59653) = (term157 _110796 _110799 _59652 f _59653).
Proof. exact (eq_refl (term157 _110796 _110799 _59652 f _59653)). Qed.
Lemma lem4813422 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term674 _110796 _110799 s r _59652 f _59653) = (term677 _110796 _110799 r _59652 f _59653 s).
Proof. exact (MK_COMB (@lem4813421 _110796 _110799 _59652 f _59653) (@lem4813415 _110796 _110799 r _59652 f _59653 s)). Qed.
Lemma lem4813426 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813427 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term677 _110796 _110799 r _59652 f _59653 s) = (term678 _110796 _110799 r _59652 f _59653 s).
Proof. exact (@lem4813426 (term152 _110796 _110799 r _59652 f _59653) ((f _59652) = (f _59653)) (term559 _110799 _59653 s)). Qed.
Lemma lem4813445 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term674 _110796 _110799 s r _59652 f _59653) = (term678 _110796 _110799 r _59652 f _59653 s).
Proof. exact (TRANS (@lem4813422 _110796 _110799 r _59652 f _59653 s) (@lem4813427 _110796 _110799 r _59652 f _59653 s)). Qed.
Lemma lem4813446 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term673 _110796 _110799 s r _59652 f _59653) = (term678 _110796 _110799 r _59652 f _59653 s).
Proof. exact (TRANS (@lem4813398 _110796 _110799 s r _59652 f _59653) (@lem4813445 _110796 _110799 r _59652 f _59653 s)). Qed.
Lemma lem4813447 {_110799 : Type'} (_59652 : _110799) (s : _110799 -> Prop) : (term143 _110799 _59652 s) = (term143 _110799 _59652 s).
Proof. exact (eq_refl (term143 _110799 _59652 s)). Qed.
Lemma lem4813448 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term697 _110796 _110799 s r _59652 f _59653) = (term698 _110796 _110799 r _59652 f _59653 s).
Proof. exact (MK_COMB (@lem4813447 _110799 _59652 s) (@lem4813446 _110796 _110799 r _59652 f _59653 s)). Qed.
Lemma lem4813452 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813453 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) (s : _110799 -> Prop) : (term698 _110796 _110799 r _59652 f _59653 s) = (term699 _110796 _110799 r _59652 f _59653 s).
Proof. exact (@lem4813452 (term152 _110796 _110799 r _59652 f _59653) (term559 _110799 _59652 s) (term681 _110796 _110799 _59652 f _59653 s)). Qed.
Lemma lem4813467 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813468 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term700 _110796 _110799 _59652 f _59653 s) = (term701 _110796 _110799 f _59652 _59653 s).
Proof. exact (@lem4813467 ((f _59652) = (f _59653)) (term559 _110799 _59652 s) (term559 _110799 _59653 s)). Qed.
Lemma lem4813486 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term684 _110796 _110799 r _59652 f _59653) = (term684 _110796 _110799 r _59652 f _59653).
Proof. exact (eq_refl (term684 _110796 _110799 r _59652 f _59653)). Qed.
Lemma lem4813487 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term699 _110796 _110799 r _59652 f _59653 s) = (term702 _110796 _110799 r f _59652 _59653 s).
Proof. exact (MK_COMB (@lem4813486 _110796 _110799 r _59652 f _59653) (@lem4813468 _110796 _110799 f _59652 _59653 s)). Qed.
Lemma lem4813498 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term698 _110796 _110799 r _59652 f _59653 s) = (term702 _110796 _110799 r f _59652 _59653 s).
Proof. exact (TRANS (@lem4813453 _110796 _110799 r _59652 f _59653 s) (@lem4813487 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813499 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term697 _110796 _110799 s r _59652 f _59653) = (term702 _110796 _110799 r f _59652 _59653 s).
Proof. exact (TRANS (@lem4813448 _110796 _110799 r _59652 f _59653 s) (@lem4813498 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813500 {_110799 : Type'} (_59652 : _110799) (_59653 : _110799) : (term602 _110799 _59652 _59653) = (term602 _110799 _59652 _59653).
Proof. exact (eq_refl (term602 _110799 _59652 _59653)). Qed.
Lemma lem4813501 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term703 _110796 _110799 s r _59652 f _59653) = (term704 _110796 _110799 r f _59652 _59653 s).
Proof. exact (MK_COMB (@lem4813500 _110799 _59652 _59653) (@lem4813499 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813505 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813506 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term704 _110796 _110799 r f _59652 _59653 s) = (term705 _110796 _110799 r f _59652 _59653 s).
Proof. exact (@lem4813505 (term152 _110796 _110799 r _59652 f _59653) (_59652 = _59653) (term701 _110796 _110799 f _59652 _59653 s)). Qed.
Lemma lem4813520 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4813521 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term706 _110796 _110799 f _59652 _59653 s) = (term693 _110796 _110799 f _59652 _59653 s).
Proof. exact (@lem4813520 ((f _59652) = (f _59653)) (_59652 = _59653) (term618 _110799 _59652 _59653 s)). Qed.
Lemma lem4813551 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term684 _110796 _110799 r _59652 f _59653) = (term684 _110796 _110799 r _59652 f _59653).
Proof. exact (eq_refl (term684 _110796 _110799 r _59652 f _59653)). Qed.
Lemma lem4813552 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term705 _110796 _110799 r f _59652 _59653 s) = (term694 _110796 _110799 r f _59652 _59653 s).
Proof. exact (MK_COMB (@lem4813551 _110796 _110799 r _59652 f _59653) (@lem4813521 _110796 _110799 f _59652 _59653 s)). Qed.
Lemma lem4813563 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term704 _110796 _110799 r f _59652 _59653 s) = (term694 _110796 _110799 r f _59652 _59653 s).
Proof. exact (TRANS (@lem4813506 _110796 _110799 r f _59652 _59653 s) (@lem4813552 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813564 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : (term703 _110796 _110799 s r _59652 f _59653) = (term694 _110796 _110799 r f _59652 _59653 s).
Proof. exact (TRANS (@lem4813501 _110796 _110799 r f _59652 _59653 s) (@lem4813563 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813565 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : ((term567 _110796 _110799 s r _59652 f _59653) = (term703 _110796 _110799 s r _59652 f _59653)) = ((term694 _110796 _110799 r f _59652 _59653 s) = (term694 _110796 _110799 r f _59652 _59653 s)).
Proof. exact (MK_COMB (@lem4813371 _110796 _110799 r f _59652 _59653 s) (@lem4813564 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813567 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4813568 (x : Prop) : (x = x) = True.
Proof. exact (@lem4813567 Prop x). Qed.
Lemma lem4813569 {_110796 _110799 : Type'} (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) (s : _110799 -> Prop) : ((term694 _110796 _110799 r f _59652 _59653 s) = (term694 _110796 _110799 r f _59652 _59653 s)) = True.
Proof. exact (@lem4813568 (term694 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813570 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : ((term567 _110796 _110799 s r _59652 f _59653) = (term703 _110796 _110799 s r _59652 f _59653)) = True.
Proof. exact (TRANS (@lem4813565 _110796 _110799 r f _59652 _59653 s) (@lem4813569 _110796 _110799 r f _59652 _59653 s)). Qed.
Lemma lem4813571 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : True = ((term567 _110796 _110799 s r _59652 f _59653) = (term703 _110796 _110799 s r _59652 f _59653)).
Proof. exact (SYM (@lem4813570 _110796 _110799 s r _59652 f _59653)). Qed.
Lemma lem4813572 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term567 _110796 _110799 s r _59652 f _59653) = (term703 _110796 _110799 s r _59652 f _59653).
Proof. exact (EQ_MP (@lem4813571 _110796 _110799 s r _59652 f _59653) (@lem0)). Qed.
Lemma lem4813573 {_110796 _110799 : Type'} (_59652 : _110799) (_59653 : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term703 _110796 _110799 s r _59652 f _59653.
Proof. exact (EQ_MP (@lem4813572 _110796 _110799 s r _59652 f _59653) (@lem4812354 _110796 _110799 _59652 _59653 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813575 (b : Prop) (a : Prop) : (a \/ b) = (term634 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4813576 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) : (term703 _110796 _110799 s r _59652 f _59653) = (term707 _110796 _110799 s r f _59652 _59653).
Proof. exact (@lem4813575 (term697 _110796 _110799 s r _59652 f _59653) (_59652 = _59653)). Qed.
Lemma lem4813578 (a : Prop) (b : Prop) : (term636 a b) = (term637 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4813579 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term708 _110796 _110799 s r _59652 f _59653) = (term709 _110796 _110799 s r _59652 f _59653).
Proof. exact (@lem4813578 (term559 _110799 _59652 s) (term673 _110796 _110799 s r _59652 f _59653)). Qed.
Lemma lem4813581 (a : Prop) : (term86 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4813582 {_110799 : Type'} (_59652 : _110799) (s : _110799 -> Prop) : (term646 _110799 _59652 s) = (@IN _110799 _59652 s).
Proof. exact (@lem4813581 (@IN _110799 _59652 s)). Qed.
Lemma lem4813583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4813584 {_110799 : Type'} (_59652 : _110799) (s : _110799 -> Prop) : (term647 _110799 _59652 s) = (term648 _110799 _59652 s).
Proof. exact (MK_COMB (@lem4813583) (@lem4813582 _110799 _59652 s)). Qed.
Lemma lem4813586 (a : Prop) (b : Prop) : (term636 a b) = (term637 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4813587 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term710 _110796 _110799 s r _59652 f _59653) = (term711 _110796 _110799 s r _59652 f _59653).
Proof. exact (@lem4813586 (term559 _110799 _59653 s) (term159 _110796 _110799 r _59652 f _59653)). Qed.
Lemma lem4813589 (a : Prop) : (term86 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4813590 {_110799 : Type'} (_59653 : _110799) (s : _110799 -> Prop) : (term646 _110799 _59653 s) = (@IN _110799 _59653 s).
Proof. exact (@lem4813589 (@IN _110799 _59653 s)). Qed.
Lemma lem4813591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4813592 {_110799 : Type'} (_59653 : _110799) (s : _110799 -> Prop) : (term647 _110799 _59653 s) = (term648 _110799 _59653 s).
Proof. exact (MK_COMB (@lem4813591) (@lem4813590 _110799 _59653 s)). Qed.
Lemma lem4813594 (a : Prop) (b : Prop) : (term636 a b) = (term637 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4813595 {_110796 _110799 : Type'} (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term712 _110796 _110799 r _59652 f _59653) = (term154 _110796 _110799 r _59652 f _59653).
Proof. exact (@lem4813594 ((f _59652) = (f _59653)) (term152 _110796 _110799 r _59652 f _59653)). Qed.
Lemma lem4813596 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term711 _110796 _110799 s r _59652 f _59653) = (term713 _110796 _110799 s r _59652 f _59653).
Proof. exact (MK_COMB (@lem4813592 _110799 _59653 s) (@lem4813595 _110796 _110799 r _59652 f _59653)). Qed.
Lemma lem4813597 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term710 _110796 _110799 s r _59652 f _59653) = (term713 _110796 _110799 s r _59652 f _59653).
Proof. exact (TRANS (@lem4813587 _110796 _110799 s r _59652 f _59653) (@lem4813596 _110796 _110799 s r _59652 f _59653)). Qed.
Lemma lem4813598 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term709 _110796 _110799 s r _59652 f _59653) = (term714 _110796 _110799 s r _59652 f _59653).
Proof. exact (MK_COMB (@lem4813584 _110799 _59652 s) (@lem4813597 _110796 _110799 s r _59652 f _59653)). Qed.
Lemma lem4813599 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term708 _110796 _110799 s r _59652 f _59653) = (term714 _110796 _110799 s r _59652 f _59653).
Proof. exact (TRANS (@lem4813579 _110796 _110799 s r _59652 f _59653) (@lem4813598 _110796 _110799 s r _59652 f _59653)). Qed.
Lemma lem4813600 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4813601 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (_59652 : _110799) (f : _110799 -> _110796) (_59653 : _110799) : (term715 _110796 _110799 s r _59652 f _59653) = (term716 _110796 _110799 s r _59652 f _59653).
Proof. exact (MK_COMB (@lem4813600) (@lem4813599 _110796 _110799 s r _59652 f _59653)). Qed.
Lemma lem4813602 {_110799 : Type'} (_59652 : _110799) (_59653 : _110799) : (_59652 = _59653) = (_59652 = _59653).
Proof. exact (eq_refl (_59652 = _59653)). Qed.
Lemma lem4813603 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) : (term707 _110796 _110799 s r f _59652 _59653) = (term717 _110796 _110799 s r f _59652 _59653).
Proof. exact (MK_COMB (@lem4813601 _110796 _110799 s r _59652 f _59653) (@lem4813602 _110799 _59652 _59653)). Qed.
Lemma lem4813604 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (_59652 : _110799) (_59653 : _110799) : (term703 _110796 _110799 s r _59652 f _59653) = (term717 _110796 _110799 s r f _59652 _59653).
Proof. exact (TRANS (@lem4813576 _110796 _110799 s r f _59652 _59653) (@lem4813603 _110796 _110799 s r f _59652 _59653)). Qed.
Lemma lem4813606 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term155 _110796 _110799 x'' f x''') (h2 : term364 _110796 _110799 x'' x''' x' y' s r f) : term154 _110796 _110799 r x'' f x'''.
Proof. exact (conj (@lem4813141 _110796 _110799 x'' f x''' h1) (@lem4813148 _110796 _110799 x'' x''' x' y' s r f h2)). Qed.
Lemma lem4813607 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term155 _110796 _110799 x'' f x''') (h2 : term364 _110796 _110799 x'' x''' x' y' s r f) : term713 _110796 _110799 s r x'' f x'''.
Proof. exact (conj (@lem4813133 _110796 _110799 x'' x''' x' y' s r f h2) (@lem4813606 _110796 _110799 x'' x''' x' y' s r f h1 h2)). Qed.
Lemma lem4813608 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term155 _110796 _110799 x'' f x''') (h2 : term364 _110796 _110799 x'' x''' x' y' s r f) : term714 _110796 _110799 s r x'' f x'''.
Proof. exact (conj (@lem4813126 _110796 _110799 x'' x''' x' y' s r f h2) (@lem4813607 _110796 _110799 x'' x''' x' y' s r f h1 h2)). Qed.
Lemma lem4813610 {_110796 _110799 : Type'} (_59652 : _110799) (_59653 : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term717 _110796 _110799 s r f _59652 _59653.
Proof. exact (EQ_MP (@lem4813604 _110796 _110799 s r f _59652 _59653) (@lem4813573 _110796 _110799 _59652 _59653 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813611 {_110796 _110799 : Type'} (_59652 : _110799) (_59653 : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term717 _110796 _110799 s r f _59652 _59653.
Proof. exact (@lem4813610 _110796 _110799 _59652 _59653 x'' x''' x' y' s r f h1). Qed.
Lemma lem4813612 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term717 _110796 _110799 s r f x'' x'''.
Proof. exact (@lem4813611 _110796 _110799 x'' x''' x'' x''' x' y' s r f h1). Qed.
Lemma lem4813615 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term155 _110796 _110799 x'' f x''') (h2 : term364 _110796 _110799 x'' x''' x' y' s r f) : x'' = x'''.
Proof. exact (@lem4813612 _110796 _110799 x'' x''' x' y' s r f h2 (@lem4813608 _110796 _110799 x'' x''' x' y' s r f h1 h2)). Qed.
Lemma lem4813616 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term155 _110796 _110799 x'' f x''') (h2 : term364 _110796 _110799 x'' x''' x' y' s r f) : term718 _110799 x'' x'''.
Proof. exact (fun h0 : term24 _110799 x'' x''' => @lem4813615 _110796 _110799 x'' x''' x' y' s r f h1 h2). Qed.
Lemma lem4813618 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4813619 {_110799 : Type'} (x'' : _110799) (x''' : _110799) : (term718 _110799 x'' x''') = (x'' = x''').
Proof. exact (@lem4813618 (x'' = x''')). Qed.
Lemma lem4813620 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term155 _110796 _110799 x'' f x''') (h2 : term364 _110796 _110799 x'' x''' x' y' s r f) : x'' = x'''.
Proof. exact (EQ_MP (@lem4813619 _110799 x'' x''') (@lem4813616 _110796 _110799 x'' x''' x' y' s r f h1 h2)). Qed.
Lemma lem4813626 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4813627 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59698 : _110799) (_59699 : _110799) : (term670 _110796 _110799 _59698 f _59699) = (term719 _110796 _110799 f _59698 _59699).
Proof. exact (@lem4813626 ((f _59698) = (f _59699)) (term24 _110799 _59698 _59699)). Qed.
Lemma lem4813637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4813638 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59698 : _110799) (_59699 : _110799) : (term720 _110796 _110799 _59698 f _59699) = (term721 _110796 _110799 f _59698 _59699).
Proof. exact (MK_COMB (@lem4813637) (@lem4813627 _110796 _110799 f _59698 _59699)). Qed.
Lemma lem4813648 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59698 : _110799) (_59699 : _110799) : (term719 _110796 _110799 f _59698 _59699) = (term719 _110796 _110799 f _59698 _59699).
Proof. exact (eq_refl (term719 _110796 _110799 f _59698 _59699)). Qed.
Lemma lem4813649 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59698 : _110799) (_59699 : _110799) : ((term670 _110796 _110799 _59698 f _59699) = (term719 _110796 _110799 f _59698 _59699)) = ((term719 _110796 _110799 f _59698 _59699) = (term719 _110796 _110799 f _59698 _59699)).
Proof. exact (MK_COMB (@lem4813638 _110796 _110799 f _59698 _59699) (@lem4813648 _110796 _110799 f _59698 _59699)). Qed.
Lemma lem4813651 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4813652 (x : Prop) : (x = x) = True.
Proof. exact (@lem4813651 Prop x). Qed.
Lemma lem4813653 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59698 : _110799) (_59699 : _110799) : ((term719 _110796 _110799 f _59698 _59699) = (term719 _110796 _110799 f _59698 _59699)) = True.
Proof. exact (@lem4813652 (term719 _110796 _110799 f _59698 _59699)). Qed.
Lemma lem4813654 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59698 : _110799) (_59699 : _110799) : ((term670 _110796 _110799 _59698 f _59699) = (term719 _110796 _110799 f _59698 _59699)) = True.
Proof. exact (TRANS (@lem4813649 _110796 _110799 f _59698 _59699) (@lem4813653 _110796 _110799 f _59698 _59699)). Qed.
Lemma lem4813655 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59698 : _110799) (_59699 : _110799) : True = ((term670 _110796 _110799 _59698 f _59699) = (term719 _110796 _110799 f _59698 _59699)).
Proof. exact (SYM (@lem4813654 _110796 _110799 f _59698 _59699)). Qed.
Lemma lem4813656 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59698 : _110799) (_59699 : _110799) : (term670 _110796 _110799 _59698 f _59699) = (term719 _110796 _110799 f _59698 _59699).
Proof. exact (EQ_MP (@lem4813655 _110796 _110799 f _59698 _59699) (@lem0)). Qed.
Lemma lem4813657 {_110796 _110799 : Type'} (f : _110799 -> _110796) (_59698 : _110799) (_59699 : _110799) : term719 _110796 _110799 f _59698 _59699.
Proof. exact (EQ_MP (@lem4813656 _110796 _110799 f _59698 _59699) (@lem4813113 _110796 _110799 _59698 f _59699)). Qed.
Lemma lem4813659 (b : Prop) (a : Prop) : (a \/ b) = (term634 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4813660 {_110796 _110799 : Type'} (_59698 : _110799) (f : _110799 -> _110796) (_59699 : _110799) : (term719 _110796 _110799 f _59698 _59699) = (term722 _110796 _110799 _59698 f _59699).
Proof. exact (@lem4813659 (term24 _110799 _59698 _59699) ((f _59698) = (f _59699))). Qed.
Lemma lem4813662 (a : Prop) : (term86 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4813663 {_110799 : Type'} (_59698 : _110799) (_59699 : _110799) : (term106 _110799 _59698 _59699) = (_59698 = _59699).
Proof. exact (@lem4813662 (_59698 = _59699)). Qed.
Lemma lem4813664 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4813665 {_110799 : Type'} (_59698 : _110799) (_59699 : _110799) : (term723 _110799 _59698 _59699) = (term724 _110799 _59698 _59699).
Proof. exact (MK_COMB (@lem4813664) (@lem4813663 _110799 _59698 _59699)). Qed.
Lemma lem4813666 {_110796 _110799 : Type'} (_59698 : _110799) (f : _110799 -> _110796) (_59699 : _110799) : ((f _59698) = (f _59699)) = ((f _59698) = (f _59699)).
Proof. exact (eq_refl ((f _59698) = (f _59699))). Qed.
Lemma lem4813667 {_110796 _110799 : Type'} (_59698 : _110799) (f : _110799 -> _110796) (_59699 : _110799) : (term722 _110796 _110799 _59698 f _59699) = (term668 _110796 _110799 _59698 f _59699).
Proof. exact (MK_COMB (@lem4813665 _110799 _59698 _59699) (@lem4813666 _110796 _110799 _59698 f _59699)). Qed.
Lemma lem4813668 {_110796 _110799 : Type'} (_59698 : _110799) (f : _110799 -> _110796) (_59699 : _110799) : (term719 _110796 _110799 f _59698 _59699) = (term668 _110796 _110799 _59698 f _59699).
Proof. exact (TRANS (@lem4813660 _110796 _110799 _59698 f _59699) (@lem4813667 _110796 _110799 _59698 f _59699)). Qed.
Lemma lem4813671 {_110796 _110799 : Type'} (_59698 : _110799) (f : _110799 -> _110796) (_59699 : _110799) : term668 _110796 _110799 _59698 f _59699.
Proof. exact (EQ_MP (@lem4813668 _110796 _110799 _59698 f _59699) (@lem4813657 _110796 _110799 f _59698 _59699)). Qed.
Lemma lem4813672 {_110796 _110799 : Type'} (_59698 : _110799) (f : _110799 -> _110796) (_59699 : _110799) : term668 _110796 _110799 _59698 f _59699.
Proof. exact (@lem4813671 _110796 _110799 _59698 f _59699). Qed.
Lemma lem4813673 {_110796 _110799 : Type'} (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : term668 _110796 _110799 x'' f x'''.
Proof. exact (@lem4813672 _110796 _110799 x'' f x'''). Qed.
Lemma lem4813676 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term155 _110796 _110799 x'' f x''') (h2 : term364 _110796 _110799 x'' x''' x' y' s r f) : (f x'') = (f x''').
Proof. exact (@lem4813673 _110796 _110799 x'' f x''' (@lem4813620 _110796 _110799 x'' x''' x' y' s r f h1 h2)). Qed.
Lemma lem4813677 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term725 _110796 _110799 x'' f x'''.
Proof. exact (fun h0 : term155 _110796 _110799 x'' f x''' => @lem4813676 _110796 _110799 x'' x''' x' y' s r f h0 h1). Qed.
Lemma lem4813679 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4813680 {_110796 _110799 : Type'} (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : (term725 _110796 _110799 x'' f x''') = ((f x'') = (f x''')).
Proof. exact (@lem4813679 ((f x'') = (f x'''))). Qed.
Lemma lem4813681 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : (f x'') = (f x''').
Proof. exact (EQ_MP (@lem4813680 _110796 _110799 x'' f x''') (@lem4813677 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813684 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4813686 {_110796 _110799 : Type'} (x'' : _110799) (f : _110799 -> _110796) (x''' : _110799) : (term155 _110796 _110799 x'' f x''') = (term726 _110796 _110799 x'' f x''').
Proof. exact (@lem4813684 ((f x'') = (f x'''))). Qed.
Lemma lem4813689 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term726 _110796 _110799 x'' f x'''.
Proof. exact (EQ_MP (@lem4813686 _110796 _110799 x'' f x''') (@lem4812380 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813692 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : False.
Proof. exact (@lem4813689 _110796 _110799 x'' x''' x' y' s r f h1 (@lem4813681 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813693 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : term667.
Proof. exact (fun h0 : ~ False => @lem4813692 _110796 _110799 x'' x''' x' y' s r f h1). Qed.
Lemma lem4813695 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4813696 : term667 = False.
Proof. exact (@lem4813695 False). Qed.
Lemma lem4813699 {_110796 _110799 : Type'} (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term364 _110796 _110799 x'' x''' x' y' s r f) : False.
Proof. exact (EQ_MP (@lem4813696) (@lem4813693 _110796 _110799 x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813700 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term453 _110796 _110799 x y x'' x''' x' y' s r f) : False.
Proof. exact (or_elim (@lem4811853 _110796 _110799 x y x'' x''' x' y' s r f h1) (fun h0 : term221 _110796 _110799 s r x f y => @lem4813067 _110796 _110799 s r x f y h0) (fun h0 : term364 _110796 _110799 x'' x''' x' y' s r f => @lem4813699 _110796 _110799 x'' x''' x' y' s r f h0)). Qed.
Lemma lem4813701 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term453 _110796 _110799 x y x'' x''' x' y' s r f) : (term453 _110796 _110799 x y x'' x''' x' y' s r f) = False.
Proof. exact (prop_ext (fun h2 : term453 _110796 _110799 x y x'' x''' x' y' s r f => @lem4813700 _110796 _110799 x y x'' x''' x' y' s r f h1) (fun h2 : False => @lem4811853 _110796 _110799 x y x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813702 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x'' : _110799) (x''' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term453 _110796 _110799 x y x'' x''' x' y' s r f) : False.
Proof. exact (EQ_MP (@lem4813701 _110796 _110799 x y x'' x''' x' y' s r f h1) (@lem4811853 _110796 _110799 x y x'' x''' x' y' s r f h1)). Qed.
Lemma lem4813703 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x'' : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term456 _110796 _110799 x y x'' x' y' s r f) : False.
Proof. exact (ex_elim (@lem4811614 _110796 _110799 x y x'' x' y' s r f h1) (fun x''' : _110799 => fun h0 : term455 _110796 _110799 x y x'' x' y' s r f x''' => @lem4813702 _110796 _110799 x y x'' x''' x' y' s r f h0)). Qed.
Lemma lem4813704 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (y' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term458 _110796 _110799 x y x' y' s r f) : False.
Proof. exact (ex_elim (@lem4811613 _110796 _110799 x y x' y' s r f h1) (fun x'' : _110799 => fun h0 : term457 _110796 _110799 x y x' y' s r f x'' => @lem4813703 _110796 _110799 x y x'' x' y' s r f h0)). Qed.
Lemma lem4813705 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (x' : _110796) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term460 _110796 _110799 x y x' s r f) : False.
Proof. exact (ex_elim (@lem4811612 _110796 _110799 x y x' s r f h1) (fun y' : _110796 => fun h0 : term459 _110796 _110799 x y x' s r f y' => @lem4813704 _110796 _110799 x y x' y' s r f h0)). Qed.
Lemma lem4813706 {_110796 _110799 : Type'} (x : _110799) (y : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term462 _110796 _110799 x y s r f) : False.
Proof. exact (ex_elim (@lem4811611 _110796 _110799 x y s r f h1) (fun x' : _110796 => fun h0 : term461 _110796 _110799 x y s r f x' => @lem4813705 _110796 _110799 x y x' s r f h0)). Qed.
Lemma lem4813707 {_110796 _110799 : Type'} (x : _110799) (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term464 _110796 _110799 x s r f) : False.
Proof. exact (ex_elim (@lem4811610 _110796 _110799 x s r f h1) (fun y : _110799 => fun h0 : term463 _110796 _110799 x s r f y => @lem4813706 _110796 _110799 x y s r f h0)). Qed.
Lemma lem4813708 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term94 _110796 _110799 s r f) : False.
Proof. exact (ex_elim (@lem4811609 _110796 _110799 s r f h1) (fun x : _110799 => fun h0 : term465 _110796 _110799 s r f x => @lem4813707 _110796 _110799 x s r f h0)). Qed.
Lemma lem4813709 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term94 _110796 _110799 s r f) : (term94 _110796 _110799 s r f) = False.
Proof. exact (prop_ext (fun h2 : term94 _110796 _110799 s r f => @lem4813708 _110796 _110799 s r f h1) (fun h2 : False => @lem4810559 _110796 _110799 s r f h1)). Qed.
Lemma lem4813710 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) (h1 : term94 _110796 _110799 s r f) : False.
Proof. exact (EQ_MP (@lem4813709 _110796 _110799 s r f h1) (@lem4810559 _110796 _110799 s r f h1)). Qed.
Lemma lem4813711 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : term93 _110796 _110799 s r f.
Proof. exact (fun h0 : term94 _110796 _110799 s r f => @lem4813710 _110796 _110799 s r f h0). Qed.
Lemma lem4813712 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) (f : _110799 -> _110796) : (term39 _110796 _110799 f s r) = (term70 _110796 _110799 s r f).
Proof. exact (EQ_MP (@lem4810558 _110796 _110799 s r f) (@lem4813711 _110796 _110799 s r f)). Qed.
Lemma lem4813717 {_110796 _110799 : Type'} (s : _110799 -> Prop) (r : type1402 _110796) : term74 _110796 _110799 s r.
Proof. exact (fun f : _110799 -> _110796 => @lem4813712 _110796 _110799 s r f). Qed.
Lemma lem4813722 {_110796 _110799 : Type'} (s : _110799 -> Prop) : term78 _110796 _110799 s.
Proof. exact (fun r : type1402 _110796 => @lem4813717 _110796 _110799 s r). Qed.
Lemma lem4813727 {_110796 _110799 : Type'} : term90 _110796 _110799.
Proof. exact (fun s : _110799 -> Prop => @lem4813722 _110796 _110799 s). Qed.
Lemma lem4813728 {_110796 _110799 : Type'} : term89 _110796 _110799.
Proof. exact (EQ_MP (@lem4810554 _110796 _110799) (@lem4813727 _110796 _110799)). Qed.
Lemma lem4813729 {_110796 _110799 : Type'} (s : _110799 -> Prop) : term727 _110796 _110799 s.
Proof. exact (@lem4813728 _110796 _110799 s). Qed.
Lemma lem4813730 {_110796 _110799 : Type'} (s : _110799 -> Prop) : (term727 _110796 _110799 s) = (term80 _110796 _110799 s).
Proof. exact (eq_refl (term727 _110796 _110799 s)). Qed.
Lemma lem4813731 {_110796 _110799 : Type'} (s : _110799 -> Prop) : term80 _110796 _110799 s.
Proof. exact (EQ_MP (@lem4813730 _110796 _110799 s) (@lem4813729 _110796 _110799 s)). Qed.
Lemma lem4813733 {_110796 _110799 : Type'} (s : _110799 -> Prop) : term80 _110796 _110799 s.
Proof. exact (@lem4810244 _110796 _110799 s (@lem4813731 _110796 _110799 s)). Qed.
Lemma lem4813734 {_110796 _110799 : Type'} (s : _110799 -> Prop) (h1 : term81 _110796 _110799 s) : False.
Proof. exact (@lem4813733 _110796 _110799 s (@lem4810228 _110796 _110799 s h1)). Qed.
Lemma lem4813735 {_110796 _110799 : Type'} (s : _110799 -> Prop) (h1 : term81 _110796 _110799 s) : (term81 _110796 _110799 s) = False.
Proof. exact (prop_ext (fun h2 : term81 _110796 _110799 s => @lem4813734 _110796 _110799 s h1) (fun h2 : False => @lem4810228 _110796 _110799 s h1)). Qed.
Lemma lem4813736 {_110796 _110799 : Type'} (s : _110799 -> Prop) (h1 : term81 _110796 _110799 s) : False.
Proof. exact (EQ_MP (@lem4813735 _110796 _110799 s h1) (@lem4810228 _110796 _110799 s h1)). Qed.
Lemma lem4813737 {_110796 _110799 : Type'} (s : _110799 -> Prop) : term80 _110796 _110799 s.
Proof. exact (fun h0 : term81 _110796 _110799 s => @lem4813736 _110796 _110799 s h0). Qed.
Lemma lem4813738 {_110796 _110799 : Type'} (s : _110799 -> Prop) : term78 _110796 _110799 s.
Proof. exact (EQ_MP (@lem4810227 _110796 _110799 s) (@lem4813737 _110796 _110799 s)). Qed.
Lemma lem4813739 {_110796 _110799 : Type'} (s : _110799 -> Prop) : term77 _110796 _110799 s.
Proof. exact (EQ_MP (@lem4810223 _110796 _110799 s) (@lem4813738 _110796 _110799 s)). Qed.

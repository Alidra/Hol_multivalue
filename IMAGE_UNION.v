Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_UNION_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import IN_UNION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3366881 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem3366882 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3366883 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3366882 A s) (@lem3366881 A s)). Qed.
Lemma lem3366884 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3366883 A s t). Qed.
Lemma lem3366885 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3366886 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term3 A s t.
Proof. exact (EQ_MP (@lem3366885 A s t) (@lem3366884 A s t)). Qed.
Lemma lem3366887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term4 A s t x.
Proof. exact (@lem3366886 A s t x). Qed.
Lemma lem3366888 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A s t x) = ((term5 A x s t) = (term6 A s x t)).
Proof. exact (eq_refl (term4 A s t x)). Qed.
Lemma lem3366890 {A B : Type'} (y : B) : term7 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3366891 {A B : Type'} (y : B) : (term7 A B y) = (term8 A B y).
Proof. exact (eq_refl (term7 A B y)). Qed.
Lemma lem3366892 {A B : Type'} (y : B) : term8 A B y.
Proof. exact (EQ_MP (@lem3366891 A B y) (@lem3366890 A B y)). Qed.
Lemma lem3366893 {A B : Type'} (y : B) (s : A -> Prop) : term9 A B y s.
Proof. exact (@lem3366892 A B y s). Qed.
Lemma lem3366894 {A B : Type'} (y : B) (s : A -> Prop) : (term9 A B y s) = (term10 A B y s).
Proof. exact (eq_refl (term9 A B y s)). Qed.
Lemma lem3366895 {A B : Type'} (y : B) (s : A -> Prop) : term10 A B y s.
Proof. exact (EQ_MP (@lem3366894 A B y s) (@lem3366893 A B y s)). Qed.
Lemma lem3366896 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term11 A B y s f.
Proof. exact (@lem3366895 A B y s f). Qed.
Lemma lem3366897 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y s f) = ((term12 A B y f s) = (term13 A B y f s)).
Proof. exact (eq_refl (term11 A B y s f)). Qed.
Lemma lem3366899 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3366900 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem3366901 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem3366900 A s) (@lem3366899 A s)). Qed.
Lemma lem3366902 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem3366901 A s t). Qed.
Lemma lem3366903 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem3366920 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3366903 A s t) (@lem3366902 A s t)). Qed.
Lemma lem3366921 {_87515 : Type'} (s : _87515 -> Prop) (t : _87515 -> Prop) : (s = t) = (term17 _87515 s t).
Proof. exact (@lem3366920 _87515 s t). Qed.
Lemma lem3366922 {_87504 _87515 : Type'} (s : _87504 -> Prop) (f : _87504 -> _87515) (t : _87504 -> Prop) : ((term18 _87504 _87515 f s t) = (term19 _87504 _87515 s f t)) = (term20 _87504 _87515 s f t).
Proof. exact (@lem3366921 _87515 (term18 _87504 _87515 f s t) (term19 _87504 _87515 s f t)). Qed.
Lemma lem3366932 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem3366897 A B y f s) (@lem3366896 A B y s f)). Qed.
Lemma lem3366933 {_87504 _87515 : Type'} (y : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term12 _87504 _87515 y f s) = (term13 _87504 _87515 y f s).
Proof. exact (@lem3366932 _87504 _87515 y f s). Qed.
Lemma lem3366934 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term21 _87504 _87515 x f s t) = (term22 _87504 _87515 x f s t).
Proof. exact (@lem3366933 _87504 _87515 x f (@UNION _87504 s t)). Qed.
Lemma lem3366946 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem3366888 A s x t) (@lem3366887 A s t x)). Qed.
Lemma lem3366947 {_87504 : Type'} (s : _87504 -> Prop) (x : _87504) (t : _87504 -> Prop) : (term5 _87504 x s t) = (term6 _87504 s x t).
Proof. exact (@lem3366946 _87504 s x t). Qed.
Lemma lem3366950 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) : (term23 _87504 _87515 x f x') = (term23 _87504 _87515 x f x').
Proof. exact (eq_refl (term23 _87504 _87515 x f x')). Qed.
Lemma lem3366951 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term24 _87504 _87515 x f x' s t) = (term25 _87504 _87515 x f s x' t).
Proof. exact (MK_COMB (@lem3366950 _87504 _87515 x f x') (@lem3366947 _87504 s x' t)). Qed.
Lemma lem3366954 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term26 _87504 _87515 x f s t) = (term27 _87504 _87515 x f s t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3366951 _87504 _87515 x f s x' t)). Qed.
Lemma lem3366955 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3366956 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term22 _87504 _87515 x f s t) = (term28 _87504 _87515 x f s t).
Proof. exact (MK_COMB (@lem3366955 _87504) (@lem3366954 _87504 _87515 x f s t)). Qed.
Lemma lem3366961 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term21 _87504 _87515 x f s t) = (term28 _87504 _87515 x f s t).
Proof. exact (TRANS (@lem3366934 _87504 _87515 x f s t) (@lem3366956 _87504 _87515 x f s t)). Qed.
Lemma lem3366962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3366963 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term29 _87504 _87515 x f s t) = (term30 _87504 _87515 x f s t).
Proof. exact (MK_COMB (@lem3366962) (@lem3366961 _87504 _87515 x f s t)). Qed.
Lemma lem3366965 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem3366888 A s x t) (@lem3366887 A s t x)). Qed.
Lemma lem3366966 {_87515 : Type'} (s : _87515 -> Prop) (x : _87515) (t : _87515 -> Prop) : (term5 _87515 x s t) = (term6 _87515 s x t).
Proof. exact (@lem3366965 _87515 s x t). Qed.
Lemma lem3366967 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term31 _87504 _87515 x s f t) = (term32 _87504 _87515 s x f t).
Proof. exact (@lem3366966 _87515 (@IMAGE _87504 _87515 f s) x (@IMAGE _87504 _87515 f t)). Qed.
Lemma lem3366971 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem3366897 A B y f s) (@lem3366896 A B y s f)). Qed.
Lemma lem3366972 {_87504 _87515 : Type'} (y : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term12 _87504 _87515 y f s) = (term13 _87504 _87515 y f s).
Proof. exact (@lem3366971 _87504 _87515 y f s). Qed.
Lemma lem3366973 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term12 _87504 _87515 x f s) = (term13 _87504 _87515 x f s).
Proof. exact (@lem3366972 _87504 _87515 x f s). Qed.
Lemma lem3366984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3366985 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term33 _87504 _87515 x f s) = (term34 _87504 _87515 x f s).
Proof. exact (MK_COMB (@lem3366984) (@lem3366973 _87504 _87515 x f s)). Qed.
Lemma lem3366987 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem3366897 A B y f s) (@lem3366896 A B y s f)). Qed.
Lemma lem3366988 {_87504 _87515 : Type'} (y : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term12 _87504 _87515 y f s) = (term13 _87504 _87515 y f s).
Proof. exact (@lem3366987 _87504 _87515 y f s). Qed.
Lemma lem3366989 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term12 _87504 _87515 x f t) = (term13 _87504 _87515 x f t).
Proof. exact (@lem3366988 _87504 _87515 x f t). Qed.
Lemma lem3367000 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term32 _87504 _87515 s x f t) = (term35 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3366985 _87504 _87515 x f s) (@lem3366989 _87504 _87515 x f t)). Qed.
Lemma lem3367003 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term31 _87504 _87515 x s f t) = (term35 _87504 _87515 s x f t).
Proof. exact (TRANS (@lem3366967 _87504 _87515 s x f t) (@lem3367000 _87504 _87515 s x f t)). Qed.
Lemma lem3367004 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : ((term21 _87504 _87515 x f s t) = (term31 _87504 _87515 x s f t)) = ((term28 _87504 _87515 x f s t) = (term35 _87504 _87515 s x f t)).
Proof. exact (MK_COMB (@lem3366963 _87504 _87515 x f s t) (@lem3367003 _87504 _87515 s x f t)). Qed.
Lemma lem3367009 {_87504 _87515 : Type'} (s : _87504 -> Prop) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term36 _87504 _87515 s f t) = (term37 _87504 _87515 s f t).
Proof. exact (fun_ext (fun x : _87515 => @lem3367004 _87504 _87515 s x f t)). Qed.
Lemma lem3367010 {_87515 : Type'} : (@all _87515) = (@all _87515).
Proof. exact (eq_refl (@all _87515)). Qed.
Lemma lem3367011 {_87504 _87515 : Type'} (s : _87504 -> Prop) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term20 _87504 _87515 s f t) = (term38 _87504 _87515 s f t).
Proof. exact (MK_COMB (@lem3367010 _87515) (@lem3367009 _87504 _87515 s f t)). Qed.
Lemma lem3367016 {_87504 _87515 : Type'} (s : _87504 -> Prop) (f : _87504 -> _87515) (t : _87504 -> Prop) : ((term18 _87504 _87515 f s t) = (term19 _87504 _87515 s f t)) = (term38 _87504 _87515 s f t).
Proof. exact (TRANS (@lem3366922 _87504 _87515 s f t) (@lem3367011 _87504 _87515 s f t)). Qed.
Lemma lem3367017 {_87504 _87515 : Type'} (s : _87504 -> Prop) (f : _87504 -> _87515) : (term39 _87504 _87515 s f) = (term40 _87504 _87515 s f).
Proof. exact (fun_ext (fun t : _87504 -> Prop => @lem3367016 _87504 _87515 s f t)). Qed.
Lemma lem3367018 {_87504 : Type'} : (@all (_87504 -> Prop)) = (@all (_87504 -> Prop)).
Proof. exact (eq_refl (@all (_87504 -> Prop))). Qed.
Lemma lem3367019 {_87504 _87515 : Type'} (s : _87504 -> Prop) (f : _87504 -> _87515) : (term41 _87504 _87515 s f) = (term42 _87504 _87515 s f).
Proof. exact (MK_COMB (@lem3367018 _87504) (@lem3367017 _87504 _87515 s f)). Qed.
Lemma lem3367024 {_87504 _87515 : Type'} (f : _87504 -> _87515) : (term43 _87504 _87515 f) = (term44 _87504 _87515 f).
Proof. exact (fun_ext (fun s : _87504 -> Prop => @lem3367019 _87504 _87515 s f)). Qed.
Lemma lem3367025 {_87504 : Type'} : (@all (_87504 -> Prop)) = (@all (_87504 -> Prop)).
Proof. exact (eq_refl (@all (_87504 -> Prop))). Qed.
Lemma lem3367026 {_87504 _87515 : Type'} (f : _87504 -> _87515) : (term45 _87504 _87515 f) = (term46 _87504 _87515 f).
Proof. exact (MK_COMB (@lem3367025 _87504) (@lem3367024 _87504 _87515 f)). Qed.
Lemma lem3367031 {_87504 _87515 : Type'} : (term47 _87504 _87515) = (term48 _87504 _87515).
Proof. exact (fun_ext (fun f : _87504 -> _87515 => @lem3367026 _87504 _87515 f)). Qed.
Lemma lem3367032 {_87504 _87515 : Type'} : (@all (_87504 -> _87515)) = (@all (_87504 -> _87515)).
Proof. exact (eq_refl (@all (_87504 -> _87515))). Qed.
Lemma lem3367033 {_87504 _87515 : Type'} : (term49 _87504 _87515) = (term50 _87504 _87515).
Proof. exact (MK_COMB (@lem3367032 _87504 _87515) (@lem3367031 _87504 _87515)). Qed.
Lemma lem3367038 {_87504 _87515 : Type'} : (term50 _87504 _87515) = (term49 _87504 _87515).
Proof. exact (SYM (@lem3367033 _87504 _87515)). Qed.
Lemma lem3367040 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3367041 {_87504 _87515 : Type'} : (term50 _87504 _87515) = (term52 _87504 _87515).
Proof. exact (@lem3367040 (term50 _87504 _87515)). Qed.
Lemma lem3367042 {_87504 _87515 : Type'} : (term52 _87504 _87515) = (term50 _87504 _87515).
Proof. exact (SYM (@lem3367041 _87504 _87515)). Qed.
Lemma lem3367043 {_87504 _87515 : Type'} (h1 : term53 _87504 _87515) : term53 _87504 _87515.
Proof. exact (h1). Qed.
Lemma lem3367046 {_87504 _87515 : Type'} (h1 : term52 _87504 _87515) : term52 _87504 _87515.
Proof. exact (h1). Qed.
Lemma lem3367047 {_87504 _87515 : Type'} : term54 _87504 _87515.
Proof. exact (fun h0 : term52 _87504 _87515 => @lem3367046 _87504 _87515 h0). Qed.
Lemma lem3367048 {_87504 _87515 : Type'} (h1 : term54 _87504 _87515) : term54 _87504 _87515.
Proof. exact (h1). Qed.
Lemma lem3367049 {_87504 _87515 : Type'} (h1 : term52 _87504 _87515) : term52 _87504 _87515.
Proof. exact (h1). Qed.
Lemma lem3367050 {_87504 _87515 : Type'} (h1 : term52 _87504 _87515) (h2 : term54 _87504 _87515) : term52 _87504 _87515.
Proof. exact (@lem3367048 _87504 _87515 h2 (@lem3367049 _87504 _87515 h1)). Qed.
Lemma lem3367051 {_87504 _87515 : Type'} (h1 : term52 _87504 _87515) : term55 _87504 _87515.
Proof. exact (fun h0 : term54 _87504 _87515 => @lem3367050 _87504 _87515 h1 h0). Qed.
Lemma lem3367052 {_87504 _87515 : Type'} (h1 : term54 _87504 _87515) : term54 _87504 _87515.
Proof. exact (h1). Qed.
Lemma lem3367053 {_87504 _87515 : Type'} (h1 : term52 _87504 _87515) (h2 : term54 _87504 _87515) : term52 _87504 _87515.
Proof. exact (@lem3367051 _87504 _87515 h1 (@lem3367052 _87504 _87515 h2)). Qed.
Lemma lem3367054 {_87504 _87515 : Type'} (h1 : term54 _87504 _87515) : term54 _87504 _87515.
Proof. exact (fun h0 : term52 _87504 _87515 => @lem3367053 _87504 _87515 h0 h1). Qed.
Lemma lem3367055 {_87504 _87515 : Type'} : term56 _87504 _87515.
Proof. exact (fun h0 : term54 _87504 _87515 => @lem3367054 _87504 _87515 h0). Qed.
Lemma lem3367058 {_87504 _87515 : Type'} : term54 _87504 _87515.
Proof. exact (@lem3367055 _87504 _87515 (@lem3367047 _87504 _87515)). Qed.
Lemma lem3367059 {_87504 _87515 : Type'} : term54 _87504 _87515.
Proof. exact (@lem3367058 _87504 _87515). Qed.
Lemma lem3367061 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3367062 {_87504 _87515 : Type'} : (term52 _87504 _87515) = (term57 _87504 _87515).
Proof. exact (@lem3367061 (term53 _87504 _87515)). Qed.
Lemma lem3367064 (t : Prop) : (term58 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3367065 {_87504 _87515 : Type'} : (term57 _87504 _87515) = (term50 _87504 _87515).
Proof. exact (@lem3367064 (term50 _87504 _87515)). Qed.
Lemma lem3367240 {_87504 _87515 : Type'} : (term52 _87504 _87515) = (term50 _87504 _87515).
Proof. exact (TRANS (@lem3367062 _87504 _87515) (@lem3367065 _87504 _87515)). Qed.
Lemma lem3367245 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term59 _87504 _87515 x f x' t) = (term59 _87504 _87515 x f x' t).
Proof. exact (eq_refl (term59 _87504 _87515 x f x' t)). Qed.
Lemma lem3367246 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term60 _87504 _87515 x f t) = (term60 _87504 _87515 x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367245 _87504 _87515 x f x' t)). Qed.
Lemma lem3367247 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367248 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term13 _87504 _87515 x f t) = (term13 _87504 _87515 x f t).
Proof. exact (MK_COMB (@lem3367247 _87504) (@lem3367246 _87504 _87515 x f t)). Qed.
Lemma lem3367253 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) : (term59 _87504 _87515 x f x' s) = (term59 _87504 _87515 x f x' s).
Proof. exact (eq_refl (term59 _87504 _87515 x f x' s)). Qed.
Lemma lem3367254 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term60 _87504 _87515 x f s) = (term60 _87504 _87515 x f s).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367253 _87504 _87515 x f x' s)). Qed.
Lemma lem3367255 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367256 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term13 _87504 _87515 x f s) = (term13 _87504 _87515 x f s).
Proof. exact (MK_COMB (@lem3367255 _87504) (@lem3367254 _87504 _87515 x f s)). Qed.
Lemma lem3367257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3367258 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term34 _87504 _87515 x f s) = (term34 _87504 _87515 x f s).
Proof. exact (MK_COMB (@lem3367257) (@lem3367256 _87504 _87515 x f s)). Qed.
Lemma lem3367259 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term35 _87504 _87515 s x f t) = (term35 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367258 _87504 _87515 x f s) (@lem3367248 _87504 _87515 x f t)). Qed.
Lemma lem3367268 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term25 _87504 _87515 x f s x' t) = (term25 _87504 _87515 x f s x' t).
Proof. exact (eq_refl (term25 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367269 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term27 _87504 _87515 x f s t) = (term27 _87504 _87515 x f s t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367268 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367270 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367271 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term28 _87504 _87515 x f s t) = (term28 _87504 _87515 x f s t).
Proof. exact (MK_COMB (@lem3367270 _87504) (@lem3367269 _87504 _87515 x f s t)). Qed.
Lemma lem3367272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3367273 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term30 _87504 _87515 x f s t) = (term30 _87504 _87515 x f s t).
Proof. exact (MK_COMB (@lem3367272) (@lem3367271 _87504 _87515 x f s t)). Qed.
Lemma lem3367274 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : ((term28 _87504 _87515 x f s t) = (term35 _87504 _87515 s x f t)) = ((term28 _87504 _87515 x f s t) = (term35 _87504 _87515 s x f t)).
Proof. exact (MK_COMB (@lem3367273 _87504 _87515 x f s t) (@lem3367259 _87504 _87515 s x f t)). Qed.
Lemma lem3367275 {_87504 _87515 : Type'} (s : _87504 -> Prop) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term37 _87504 _87515 s f t) = (term37 _87504 _87515 s f t).
Proof. exact (fun_ext (fun x : _87515 => @lem3367274 _87504 _87515 s x f t)). Qed.
Lemma lem3367276 {_87515 : Type'} : (@all _87515) = (@all _87515).
Proof. exact (eq_refl (@all _87515)). Qed.
Lemma lem3367277 {_87504 _87515 : Type'} (s : _87504 -> Prop) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term38 _87504 _87515 s f t) = (term38 _87504 _87515 s f t).
Proof. exact (MK_COMB (@lem3367276 _87515) (@lem3367275 _87504 _87515 s f t)). Qed.
Lemma lem3367278 {_87504 _87515 : Type'} (s : _87504 -> Prop) (f : _87504 -> _87515) : (term40 _87504 _87515 s f) = (term40 _87504 _87515 s f).
Proof. exact (fun_ext (fun t : _87504 -> Prop => @lem3367277 _87504 _87515 s f t)). Qed.
Lemma lem3367279 {_87504 : Type'} : (@all (_87504 -> Prop)) = (@all (_87504 -> Prop)).
Proof. exact (eq_refl (@all (_87504 -> Prop))). Qed.
Lemma lem3367280 {_87504 _87515 : Type'} (s : _87504 -> Prop) (f : _87504 -> _87515) : (term42 _87504 _87515 s f) = (term42 _87504 _87515 s f).
Proof. exact (MK_COMB (@lem3367279 _87504) (@lem3367278 _87504 _87515 s f)). Qed.
Lemma lem3367281 {_87504 _87515 : Type'} (f : _87504 -> _87515) : (term44 _87504 _87515 f) = (term44 _87504 _87515 f).
Proof. exact (fun_ext (fun s : _87504 -> Prop => @lem3367280 _87504 _87515 s f)). Qed.
Lemma lem3367282 {_87504 : Type'} : (@all (_87504 -> Prop)) = (@all (_87504 -> Prop)).
Proof. exact (eq_refl (@all (_87504 -> Prop))). Qed.
Lemma lem3367283 {_87504 _87515 : Type'} (f : _87504 -> _87515) : (term46 _87504 _87515 f) = (term46 _87504 _87515 f).
Proof. exact (MK_COMB (@lem3367282 _87504) (@lem3367281 _87504 _87515 f)). Qed.
Lemma lem3367284 {_87504 _87515 : Type'} : (term48 _87504 _87515) = (term48 _87504 _87515).
Proof. exact (fun_ext (fun f : _87504 -> _87515 => @lem3367283 _87504 _87515 f)). Qed.
Lemma lem3367285 {_87504 _87515 : Type'} : (@all (_87504 -> _87515)) = (@all (_87504 -> _87515)).
Proof. exact (eq_refl (@all (_87504 -> _87515))). Qed.
Lemma lem3367286 {_87504 _87515 : Type'} : (term50 _87504 _87515) = (term50 _87504 _87515).
Proof. exact (MK_COMB (@lem3367285 _87504 _87515) (@lem3367284 _87504 _87515)). Qed.
Lemma lem3367341 {_87504 _87515 : Type'} : (term52 _87504 _87515) = (term50 _87504 _87515).
Proof. exact (TRANS (@lem3367240 _87504 _87515) (@lem3367286 _87504 _87515)). Qed.
Lemma lem3367342 {_87504 _87515 : Type'} : (term50 _87504 _87515) = (term52 _87504 _87515).
Proof. exact (SYM (@lem3367341 _87504 _87515)). Qed.
Lemma lem3367344 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3367345 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : ((term28 _87504 _87515 x f s t) = (term35 _87504 _87515 s x f t)) = (term61 _87504 _87515 s x f t).
Proof. exact (@lem3367344 ((term28 _87504 _87515 x f s t) = (term35 _87504 _87515 s x f t))). Qed.
Lemma lem3367346 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term61 _87504 _87515 s x f t) = ((term28 _87504 _87515 x f s t) = (term35 _87504 _87515 s x f t)).
Proof. exact (SYM (@lem3367345 _87504 _87515 s x f t)). Qed.
Lemma lem3367347 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term62 _87504 _87515 s x f t) : term62 _87504 _87515 s x f t.
Proof. exact (h1). Qed.
Lemma lem3367358 {_87504 : Type'} (s : _87504 -> Prop) (x : _87504) (t : _87504 -> Prop) : (term63 _87504 s x t) = (term64 _87504 s x t).
Proof. exact (@lem17160 (@IN _87504 x s) (@IN _87504 x t)). Qed.
Lemma lem3367363 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) : (term65 _87504 _87515 x f x') = (term65 _87504 _87515 x f x').
Proof. exact (eq_refl (term65 _87504 _87515 x f x')). Qed.
Lemma lem3367364 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term66 _87504 _87515 x f s x' t) = (term67 _87504 _87515 x f s x' t).
Proof. exact (MK_COMB (@lem3367363 _87504 _87515 x f x') (@lem3367358 _87504 s x' t)). Qed.
Lemma lem3367365 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term68 _87504 _87515 x f s x' t) = (term66 _87504 _87515 x f s x' t).
Proof. exact (@lem17045 (x = (f x')) (term6 _87504 s x' t)). Qed.
Lemma lem3367366 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term68 _87504 _87515 x f s x' t) = (term67 _87504 _87515 x f s x' t).
Proof. exact (TRANS (@lem3367365 _87504 _87515 x f s x' t) (@lem3367364 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367369 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term25 _87504 _87515 x f s x' t) = (term25 _87504 _87515 x f s x' t).
Proof. exact (eq_refl (term25 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367370 {_87504 : Type'} (P : _87504 -> Prop) : (term69 _87504 P) = (term70 _87504 P).
Proof. exact (@lem18394 _87504 P). Qed.
Lemma lem3367371 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term71 _87504 _87515 x f s t) = (term72 _87504 _87515 x f s t).
Proof. exact (@lem3367370 _87504 (term27 _87504 _87515 x f s t)). Qed.
Lemma lem3367372 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term73 _87504 _87515 x f s t x') = (term25 _87504 _87515 x f s x' t).
Proof. exact (eq_refl (term73 _87504 _87515 x f s t x')). Qed.
Lemma lem3367373 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3367374 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term74 _87504 _87515 x f s t x') = (term68 _87504 _87515 x f s x' t).
Proof. exact (MK_COMB (@lem3367373) (@lem3367372 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367375 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term74 _87504 _87515 x f s t x') = (term67 _87504 _87515 x f s x' t).
Proof. exact (TRANS (@lem3367374 _87504 _87515 x f s x' t) (@lem3367366 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367376 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term75 _87504 _87515 x f s t) = (term76 _87504 _87515 x f s t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367375 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367377 {_87504 : Type'} : (@all _87504) = (@all _87504).
Proof. exact (eq_refl (@all _87504)). Qed.
Lemma lem3367378 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term72 _87504 _87515 x f s t) = (term77 _87504 _87515 x f s t).
Proof. exact (MK_COMB (@lem3367377 _87504) (@lem3367376 _87504 _87515 x f s t)). Qed.
Lemma lem3367379 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term71 _87504 _87515 x f s t) = (term77 _87504 _87515 x f s t).
Proof. exact (TRANS (@lem3367371 _87504 _87515 x f s t) (@lem3367378 _87504 _87515 x f s t)). Qed.
Lemma lem3367380 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term27 _87504 _87515 x f s t) = (term27 _87504 _87515 x f s t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367369 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367381 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367382 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term28 _87504 _87515 x f s t) = (term28 _87504 _87515 x f s t).
Proof. exact (MK_COMB (@lem3367381 _87504) (@lem3367380 _87504 _87515 x f s t)). Qed.
Lemma lem3367391 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) : (term78 _87504 _87515 x f x' s) = (term79 _87504 _87515 x f x' s).
Proof. exact (@lem17045 (x = (f x')) (@IN _87504 x' s)). Qed.
Lemma lem3367394 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) : (term59 _87504 _87515 x f x' s) = (term59 _87504 _87515 x f x' s).
Proof. exact (eq_refl (term59 _87504 _87515 x f x' s)). Qed.
Lemma lem3367395 {_87504 : Type'} (P : _87504 -> Prop) : (term69 _87504 P) = (term70 _87504 P).
Proof. exact (@lem18394 _87504 P). Qed.
Lemma lem3367396 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term80 _87504 _87515 x f s) = (term81 _87504 _87515 x f s).
Proof. exact (@lem3367395 _87504 (term60 _87504 _87515 x f s)). Qed.
Lemma lem3367397 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) : (term82 _87504 _87515 x f s x') = (term59 _87504 _87515 x f x' s).
Proof. exact (eq_refl (term82 _87504 _87515 x f s x')). Qed.
Lemma lem3367398 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3367399 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) : (term83 _87504 _87515 x f s x') = (term78 _87504 _87515 x f x' s).
Proof. exact (MK_COMB (@lem3367398) (@lem3367397 _87504 _87515 x f x' s)). Qed.
Lemma lem3367400 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) : (term83 _87504 _87515 x f s x') = (term79 _87504 _87515 x f x' s).
Proof. exact (TRANS (@lem3367399 _87504 _87515 x f x' s) (@lem3367391 _87504 _87515 x f x' s)). Qed.
Lemma lem3367401 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term84 _87504 _87515 x f s) = (term85 _87504 _87515 x f s).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367400 _87504 _87515 x f x' s)). Qed.
Lemma lem3367402 {_87504 : Type'} : (@all _87504) = (@all _87504).
Proof. exact (eq_refl (@all _87504)). Qed.
Lemma lem3367403 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term81 _87504 _87515 x f s) = (term86 _87504 _87515 x f s).
Proof. exact (MK_COMB (@lem3367402 _87504) (@lem3367401 _87504 _87515 x f s)). Qed.
Lemma lem3367404 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term80 _87504 _87515 x f s) = (term86 _87504 _87515 x f s).
Proof. exact (TRANS (@lem3367396 _87504 _87515 x f s) (@lem3367403 _87504 _87515 x f s)). Qed.
Lemma lem3367405 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term60 _87504 _87515 x f s) = (term60 _87504 _87515 x f s).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367394 _87504 _87515 x f x' s)). Qed.
Lemma lem3367406 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367407 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term13 _87504 _87515 x f s) = (term13 _87504 _87515 x f s).
Proof. exact (MK_COMB (@lem3367406 _87504) (@lem3367405 _87504 _87515 x f s)). Qed.
Lemma lem3367416 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term78 _87504 _87515 x f x' t) = (term79 _87504 _87515 x f x' t).
Proof. exact (@lem17045 (x = (f x')) (@IN _87504 x' t)). Qed.
Lemma lem3367419 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term59 _87504 _87515 x f x' t) = (term59 _87504 _87515 x f x' t).
Proof. exact (eq_refl (term59 _87504 _87515 x f x' t)). Qed.
Lemma lem3367420 {_87504 : Type'} (P : _87504 -> Prop) : (term69 _87504 P) = (term70 _87504 P).
Proof. exact (@lem18394 _87504 P). Qed.
Lemma lem3367421 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term80 _87504 _87515 x f t) = (term81 _87504 _87515 x f t).
Proof. exact (@lem3367420 _87504 (term60 _87504 _87515 x f t)). Qed.
Lemma lem3367422 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term82 _87504 _87515 x f t x') = (term59 _87504 _87515 x f x' t).
Proof. exact (eq_refl (term82 _87504 _87515 x f t x')). Qed.
Lemma lem3367423 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3367424 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term83 _87504 _87515 x f t x') = (term78 _87504 _87515 x f x' t).
Proof. exact (MK_COMB (@lem3367423) (@lem3367422 _87504 _87515 x f x' t)). Qed.
Lemma lem3367425 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term83 _87504 _87515 x f t x') = (term79 _87504 _87515 x f x' t).
Proof. exact (TRANS (@lem3367424 _87504 _87515 x f x' t) (@lem3367416 _87504 _87515 x f x' t)). Qed.
Lemma lem3367426 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term84 _87504 _87515 x f t) = (term85 _87504 _87515 x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367425 _87504 _87515 x f x' t)). Qed.
Lemma lem3367427 {_87504 : Type'} : (@all _87504) = (@all _87504).
Proof. exact (eq_refl (@all _87504)). Qed.
Lemma lem3367428 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term81 _87504 _87515 x f t) = (term86 _87504 _87515 x f t).
Proof. exact (MK_COMB (@lem3367427 _87504) (@lem3367426 _87504 _87515 x f t)). Qed.
Lemma lem3367429 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term80 _87504 _87515 x f t) = (term86 _87504 _87515 x f t).
Proof. exact (TRANS (@lem3367421 _87504 _87515 x f t) (@lem3367428 _87504 _87515 x f t)). Qed.
Lemma lem3367430 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term60 _87504 _87515 x f t) = (term60 _87504 _87515 x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367419 _87504 _87515 x f x' t)). Qed.
Lemma lem3367431 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367432 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term13 _87504 _87515 x f t) = (term13 _87504 _87515 x f t).
Proof. exact (MK_COMB (@lem3367431 _87504) (@lem3367430 _87504 _87515 x f t)). Qed.
Lemma lem3367433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3367434 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term87 _87504 _87515 x f s) = (term88 _87504 _87515 x f s).
Proof. exact (MK_COMB (@lem3367433) (@lem3367404 _87504 _87515 x f s)). Qed.
Lemma lem3367435 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term89 _87504 _87515 s x f t) = (term90 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367434 _87504 _87515 x f s) (@lem3367429 _87504 _87515 x f t)). Qed.
Lemma lem3367436 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term91 _87504 _87515 s x f t) = (term89 _87504 _87515 s x f t).
Proof. exact (@lem17160 (term13 _87504 _87515 x f s) (term13 _87504 _87515 x f t)). Qed.
Lemma lem3367437 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term91 _87504 _87515 s x f t) = (term90 _87504 _87515 s x f t).
Proof. exact (TRANS (@lem3367436 _87504 _87515 s x f t) (@lem3367435 _87504 _87515 s x f t)). Qed.
Lemma lem3367438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3367439 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term34 _87504 _87515 x f s) = (term34 _87504 _87515 x f s).
Proof. exact (MK_COMB (@lem3367438) (@lem3367407 _87504 _87515 x f s)). Qed.
Lemma lem3367440 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term35 _87504 _87515 s x f t) = (term35 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367439 _87504 _87515 x f s) (@lem3367432 _87504 _87515 x f t)). Qed.
Lemma lem3367441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3367442 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term92 _87504 _87515 x f s t) = (term93 _87504 _87515 x f s t).
Proof. exact (MK_COMB (@lem3367441) (@lem3367379 _87504 _87515 x f s t)). Qed.
Lemma lem3367443 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term94 _87504 _87515 s x f t) = (term95 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367442 _87504 _87515 x f s t) (@lem3367440 _87504 _87515 s x f t)). Qed.
Lemma lem3367444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3367445 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term96 _87504 _87515 x f s t) = (term96 _87504 _87515 x f s t).
Proof. exact (MK_COMB (@lem3367444) (@lem3367382 _87504 _87515 x f s t)). Qed.
Lemma lem3367446 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term97 _87504 _87515 s x f t) = (term98 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367445 _87504 _87515 x f s t) (@lem3367437 _87504 _87515 s x f t)). Qed.
Lemma lem3367447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3367448 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term99 _87504 _87515 s x f t) = (term100 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367447) (@lem3367446 _87504 _87515 s x f t)). Qed.
Lemma lem3367449 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term101 _87504 _87515 s x f t) = (term102 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367448 _87504 _87515 s x f t) (@lem3367443 _87504 _87515 s x f t)). Qed.
Lemma lem3367450 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term62 _87504 _87515 s x f t) = (term101 _87504 _87515 s x f t).
Proof. exact (@lem17646 (term28 _87504 _87515 x f s t) (term35 _87504 _87515 s x f t)). Qed.
Lemma lem3367451 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term62 _87504 _87515 s x f t) = (term102 _87504 _87515 s x f t).
Proof. exact (TRANS (@lem3367450 _87504 _87515 s x f t) (@lem3367449 _87504 _87515 s x f t)). Qed.
Lemma lem3367742 {A : Type'} (P : A -> Prop) (Q : Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3367743 {_87504 : Type'} (P : _87504 -> Prop) (Q : Prop) : (term103 _87504 P Q) = (term104 _87504 P Q).
Proof. exact (@lem3367742 _87504 P Q). Qed.
Lemma lem3367744 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term105 _87504 _87515 s x f t) = (term106 _87504 _87515 s x f t).
Proof. exact (@lem3367743 _87504 (term27 _87504 _87515 x f s t) (term90 _87504 _87515 s x f t)). Qed.
Lemma lem3367745 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term73 _87504 _87515 x f s t x') = (term25 _87504 _87515 x f s x' t).
Proof. exact (eq_refl (term73 _87504 _87515 x f s t x')). Qed.
Lemma lem3367746 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term107 _87504 _87515 x f s t) = (term27 _87504 _87515 x f s t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367745 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367747 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367748 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term108 _87504 _87515 x f s t) = (term28 _87504 _87515 x f s t).
Proof. exact (MK_COMB (@lem3367747 _87504) (@lem3367746 _87504 _87515 x f s t)). Qed.
Lemma lem3367749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3367750 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term109 _87504 _87515 x f s t) = (term96 _87504 _87515 x f s t).
Proof. exact (MK_COMB (@lem3367749) (@lem3367748 _87504 _87515 x f s t)). Qed.
Lemma lem3367751 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term90 _87504 _87515 s x f t) = (term90 _87504 _87515 s x f t).
Proof. exact (eq_refl (term90 _87504 _87515 s x f t)). Qed.
Lemma lem3367752 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term105 _87504 _87515 s x f t) = (term98 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367750 _87504 _87515 x f s t) (@lem3367751 _87504 _87515 s x f t)). Qed.
Lemma lem3367753 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3367754 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term110 _87504 _87515 s x f t) = (term111 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367753) (@lem3367752 _87504 _87515 s x f t)). Qed.
Lemma lem3367755 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term73 _87504 _87515 x f s t x') = (term25 _87504 _87515 x f s x' t).
Proof. exact (eq_refl (term73 _87504 _87515 x f s t x')). Qed.
Lemma lem3367756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3367757 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term112 _87504 _87515 x f s t x') = (term113 _87504 _87515 x f s x' t).
Proof. exact (MK_COMB (@lem3367756) (@lem3367755 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367758 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term90 _87504 _87515 s x f t) = (term90 _87504 _87515 s x f t).
Proof. exact (eq_refl (term90 _87504 _87515 s x f t)). Qed.
Lemma lem3367759 {_87504 _87515 : Type'} (x : _87504) (s : _87504 -> Prop) (x' : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term114 _87504 _87515 x s x' f t) = (term115 _87504 _87515 x s x' f t).
Proof. exact (MK_COMB (@lem3367757 _87504 _87515 x' f s x t) (@lem3367758 _87504 _87515 s x' f t)). Qed.
Lemma lem3367760 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term116 _87504 _87515 s x f t) = (term117 _87504 _87515 s x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367759 _87504 _87515 x' s x f t)). Qed.
Lemma lem3367761 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367762 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term106 _87504 _87515 s x f t) = (term118 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367761 _87504) (@lem3367760 _87504 _87515 s x f t)). Qed.
Lemma lem3367763 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : ((term105 _87504 _87515 s x f t) = (term106 _87504 _87515 s x f t)) = ((term98 _87504 _87515 s x f t) = (term118 _87504 _87515 s x f t)).
Proof. exact (MK_COMB (@lem3367754 _87504 _87515 s x f t) (@lem3367762 _87504 _87515 s x f t)). Qed.
Lemma lem3367764 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term98 _87504 _87515 s x f t) = (term118 _87504 _87515 s x f t).
Proof. exact (EQ_MP (@lem3367763 _87504 _87515 s x f t) (@lem3367744 _87504 _87515 s x f t)). Qed.
Lemma lem3367765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3367766 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term100 _87504 _87515 s x f t) = (term119 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367765) (@lem3367764 _87504 _87515 s x f t)). Qed.
Lemma lem3367768 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term121 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3367769 {_87504 : Type'} (P : _87504 -> Prop) (Q : _87504 -> Prop) : (term120 _87504 P Q) = (term121 _87504 P Q).
Proof. exact (@lem3367768 _87504 P Q). Qed.
Lemma lem3367770 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term122 _87504 _87515 s x f t) = (term123 _87504 _87515 s x f t).
Proof. exact (@lem3367769 _87504 (term60 _87504 _87515 x f s) (term60 _87504 _87515 x f t)). Qed.
Lemma lem3367771 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) : (term82 _87504 _87515 x f s x') = (term59 _87504 _87515 x f x' s).
Proof. exact (eq_refl (term82 _87504 _87515 x f s x')). Qed.
Lemma lem3367772 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term124 _87504 _87515 x f s) = (term60 _87504 _87515 x f s).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367771 _87504 _87515 x f x' s)). Qed.
Lemma lem3367773 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367774 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term125 _87504 _87515 x f s) = (term13 _87504 _87515 x f s).
Proof. exact (MK_COMB (@lem3367773 _87504) (@lem3367772 _87504 _87515 x f s)). Qed.
Lemma lem3367775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3367776 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term126 _87504 _87515 x f s) = (term34 _87504 _87515 x f s).
Proof. exact (MK_COMB (@lem3367775) (@lem3367774 _87504 _87515 x f s)). Qed.
Lemma lem3367777 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term82 _87504 _87515 x f t x') = (term59 _87504 _87515 x f x' t).
Proof. exact (eq_refl (term82 _87504 _87515 x f t x')). Qed.
Lemma lem3367778 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term124 _87504 _87515 x f t) = (term60 _87504 _87515 x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367777 _87504 _87515 x f x' t)). Qed.
Lemma lem3367779 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367780 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term125 _87504 _87515 x f t) = (term13 _87504 _87515 x f t).
Proof. exact (MK_COMB (@lem3367779 _87504) (@lem3367778 _87504 _87515 x f t)). Qed.
Lemma lem3367781 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term122 _87504 _87515 s x f t) = (term35 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367776 _87504 _87515 x f s) (@lem3367780 _87504 _87515 x f t)). Qed.
Lemma lem3367782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3367783 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term127 _87504 _87515 s x f t) = (term128 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367782) (@lem3367781 _87504 _87515 s x f t)). Qed.
Lemma lem3367784 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) : (term82 _87504 _87515 x f s x') = (term59 _87504 _87515 x f x' s).
Proof. exact (eq_refl (term82 _87504 _87515 x f s x')). Qed.
Lemma lem3367785 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3367786 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) : (term129 _87504 _87515 x f s x') = (term130 _87504 _87515 x f x' s).
Proof. exact (MK_COMB (@lem3367785) (@lem3367784 _87504 _87515 x f x' s)). Qed.
Lemma lem3367787 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term82 _87504 _87515 x f t x') = (term59 _87504 _87515 x f x' t).
Proof. exact (eq_refl (term82 _87504 _87515 x f t x')). Qed.
Lemma lem3367788 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term131 _87504 _87515 s x f t x') = (term132 _87504 _87515 s x f x' t).
Proof. exact (MK_COMB (@lem3367786 _87504 _87515 x f x' s) (@lem3367787 _87504 _87515 x f x' t)). Qed.
Lemma lem3367789 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term133 _87504 _87515 s x f t) = (term134 _87504 _87515 s x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367788 _87504 _87515 s x f x' t)). Qed.
Lemma lem3367790 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367791 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term123 _87504 _87515 s x f t) = (term135 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367790 _87504) (@lem3367789 _87504 _87515 s x f t)). Qed.
Lemma lem3367792 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : ((term122 _87504 _87515 s x f t) = (term123 _87504 _87515 s x f t)) = ((term35 _87504 _87515 s x f t) = (term135 _87504 _87515 s x f t)).
Proof. exact (MK_COMB (@lem3367783 _87504 _87515 s x f t) (@lem3367791 _87504 _87515 s x f t)). Qed.
Lemma lem3367793 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term35 _87504 _87515 s x f t) = (term135 _87504 _87515 s x f t).
Proof. exact (EQ_MP (@lem3367792 _87504 _87515 s x f t) (@lem3367770 _87504 _87515 s x f t)). Qed.
Lemma lem3367794 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term93 _87504 _87515 x f s t) = (term93 _87504 _87515 x f s t).
Proof. exact (eq_refl (term93 _87504 _87515 x f s t)). Qed.
Lemma lem3367795 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term95 _87504 _87515 s x f t) = (term136 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367794 _87504 _87515 x f s t) (@lem3367793 _87504 _87515 s x f t)). Qed.
Lemma lem3367797 {A : Type'} (P : Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3367798 {_87504 : Type'} (P : Prop) (Q : _87504 -> Prop) : (term137 _87504 P Q) = (term138 _87504 P Q).
Proof. exact (@lem3367797 _87504 P Q). Qed.
Lemma lem3367799 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term139 _87504 _87515 s x f t) = (term140 _87504 _87515 s x f t).
Proof. exact (@lem3367798 _87504 (term77 _87504 _87515 x f s t) (term134 _87504 _87515 s x f t)). Qed.
Lemma lem3367800 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term141 _87504 _87515 s x f t x') = (term132 _87504 _87515 s x f x' t).
Proof. exact (eq_refl (term141 _87504 _87515 s x f t x')). Qed.
Lemma lem3367801 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term142 _87504 _87515 s x f t) = (term134 _87504 _87515 s x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367800 _87504 _87515 s x f x' t)). Qed.
Lemma lem3367802 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367803 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term143 _87504 _87515 s x f t) = (term135 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367802 _87504) (@lem3367801 _87504 _87515 s x f t)). Qed.
Lemma lem3367804 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term93 _87504 _87515 x f s t) = (term93 _87504 _87515 x f s t).
Proof. exact (eq_refl (term93 _87504 _87515 x f s t)). Qed.
Lemma lem3367805 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term139 _87504 _87515 s x f t) = (term136 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367804 _87504 _87515 x f s t) (@lem3367803 _87504 _87515 s x f t)). Qed.
Lemma lem3367806 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3367807 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term144 _87504 _87515 s x f t) = (term145 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367806) (@lem3367805 _87504 _87515 s x f t)). Qed.
Lemma lem3367808 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term141 _87504 _87515 s x f t x') = (term132 _87504 _87515 s x f x' t).
Proof. exact (eq_refl (term141 _87504 _87515 s x f t x')). Qed.
Lemma lem3367809 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term93 _87504 _87515 x f s t) = (term93 _87504 _87515 x f s t).
Proof. exact (eq_refl (term93 _87504 _87515 x f s t)). Qed.
Lemma lem3367810 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term146 _87504 _87515 s x f t x') = (term147 _87504 _87515 s x f x' t).
Proof. exact (MK_COMB (@lem3367809 _87504 _87515 x f s t) (@lem3367808 _87504 _87515 s x f x' t)). Qed.
Lemma lem3367811 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term148 _87504 _87515 s x f t) = (term149 _87504 _87515 s x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367810 _87504 _87515 s x f x' t)). Qed.
Lemma lem3367812 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367813 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term140 _87504 _87515 s x f t) = (term150 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367812 _87504) (@lem3367811 _87504 _87515 s x f t)). Qed.
Lemma lem3367814 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : ((term139 _87504 _87515 s x f t) = (term140 _87504 _87515 s x f t)) = ((term136 _87504 _87515 s x f t) = (term150 _87504 _87515 s x f t)).
Proof. exact (MK_COMB (@lem3367807 _87504 _87515 s x f t) (@lem3367813 _87504 _87515 s x f t)). Qed.
Lemma lem3367815 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term136 _87504 _87515 s x f t) = (term150 _87504 _87515 s x f t).
Proof. exact (EQ_MP (@lem3367814 _87504 _87515 s x f t) (@lem3367799 _87504 _87515 s x f t)). Qed.
Lemma lem3367816 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term95 _87504 _87515 s x f t) = (term150 _87504 _87515 s x f t).
Proof. exact (TRANS (@lem3367795 _87504 _87515 s x f t) (@lem3367815 _87504 _87515 s x f t)). Qed.
Lemma lem3367817 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term102 _87504 _87515 s x f t) = (term151 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367766 _87504 _87515 s x f t) (@lem3367816 _87504 _87515 s x f t)). Qed.
Lemma lem3367819 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term121 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3367820 {_87504 : Type'} (P : _87504 -> Prop) (Q : _87504 -> Prop) : (term120 _87504 P Q) = (term121 _87504 P Q).
Proof. exact (@lem3367819 _87504 P Q). Qed.
Lemma lem3367821 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term152 _87504 _87515 s x f t) = (term153 _87504 _87515 s x f t).
Proof. exact (@lem3367820 _87504 (term117 _87504 _87515 s x f t) (term149 _87504 _87515 s x f t)). Qed.
Lemma lem3367822 {_87504 _87515 : Type'} (x : _87504) (s : _87504 -> Prop) (x' : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term154 _87504 _87515 s x' f t x) = (term115 _87504 _87515 x s x' f t).
Proof. exact (eq_refl (term154 _87504 _87515 s x' f t x)). Qed.
Lemma lem3367823 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term155 _87504 _87515 s x f t) = (term117 _87504 _87515 s x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367822 _87504 _87515 x' s x f t)). Qed.
Lemma lem3367824 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367825 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term156 _87504 _87515 s x f t) = (term118 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367824 _87504) (@lem3367823 _87504 _87515 s x f t)). Qed.
Lemma lem3367826 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3367827 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term157 _87504 _87515 s x f t) = (term119 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367826) (@lem3367825 _87504 _87515 s x f t)). Qed.
Lemma lem3367828 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term158 _87504 _87515 s x f t x') = (term147 _87504 _87515 s x f x' t).
Proof. exact (eq_refl (term158 _87504 _87515 s x f t x')). Qed.
Lemma lem3367829 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term159 _87504 _87515 s x f t) = (term149 _87504 _87515 s x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367828 _87504 _87515 s x f x' t)). Qed.
Lemma lem3367830 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367831 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term160 _87504 _87515 s x f t) = (term150 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367830 _87504) (@lem3367829 _87504 _87515 s x f t)). Qed.
Lemma lem3367832 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term152 _87504 _87515 s x f t) = (term151 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367827 _87504 _87515 s x f t) (@lem3367831 _87504 _87515 s x f t)). Qed.
Lemma lem3367833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3367834 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term161 _87504 _87515 s x f t) = (term162 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367833) (@lem3367832 _87504 _87515 s x f t)). Qed.
Lemma lem3367835 {_87504 _87515 : Type'} (x : _87504) (s : _87504 -> Prop) (x' : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term154 _87504 _87515 s x' f t x) = (term115 _87504 _87515 x s x' f t).
Proof. exact (eq_refl (term154 _87504 _87515 s x' f t x)). Qed.
Lemma lem3367836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3367837 {_87504 _87515 : Type'} (x : _87504) (s : _87504 -> Prop) (x' : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term163 _87504 _87515 s x' f t x) = (term164 _87504 _87515 x s x' f t).
Proof. exact (MK_COMB (@lem3367836) (@lem3367835 _87504 _87515 x s x' f t)). Qed.
Lemma lem3367838 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term158 _87504 _87515 s x f t x') = (term147 _87504 _87515 s x f x' t).
Proof. exact (eq_refl (term158 _87504 _87515 s x f t x')). Qed.
Lemma lem3367839 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term165 _87504 _87515 s x f t x') = (term166 _87504 _87515 s x f x' t).
Proof. exact (MK_COMB (@lem3367837 _87504 _87515 x' s x f t) (@lem3367838 _87504 _87515 s x f x' t)). Qed.
Lemma lem3367840 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term167 _87504 _87515 s x f t) = (term168 _87504 _87515 s x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367839 _87504 _87515 s x f x' t)). Qed.
Lemma lem3367841 {_87504 : Type'} : (@ex _87504) = (@ex _87504).
Proof. exact (eq_refl (@ex _87504)). Qed.
Lemma lem3367842 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term153 _87504 _87515 s x f t) = (term169 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367841 _87504) (@lem3367840 _87504 _87515 s x f t)). Qed.
Lemma lem3367843 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : ((term152 _87504 _87515 s x f t) = (term153 _87504 _87515 s x f t)) = ((term151 _87504 _87515 s x f t) = (term169 _87504 _87515 s x f t)).
Proof. exact (MK_COMB (@lem3367834 _87504 _87515 s x f t) (@lem3367842 _87504 _87515 s x f t)). Qed.
Lemma lem3367844 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term151 _87504 _87515 s x f t) = (term169 _87504 _87515 s x f t).
Proof. exact (EQ_MP (@lem3367843 _87504 _87515 s x f t) (@lem3367821 _87504 _87515 s x f t)). Qed.
Lemma lem3367846 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term102 _87504 _87515 s x f t) = (term169 _87504 _87515 s x f t).
Proof. exact (TRANS (@lem3367817 _87504 _87515 s x f t) (@lem3367844 _87504 _87515 s x f t)). Qed.
Lemma lem3367847 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term62 _87504 _87515 s x f t) = (term169 _87504 _87515 s x f t).
Proof. exact (TRANS (@lem3367451 _87504 _87515 s x f t) (@lem3367846 _87504 _87515 s x f t)). Qed.
Lemma lem3367848 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term62 _87504 _87515 s x f t) : term169 _87504 _87515 s x f t.
Proof. exact (EQ_MP (@lem3367847 _87504 _87515 s x f t) (@lem3367347 _87504 _87515 s x f t h1)). Qed.
Lemma lem3367849 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term166 _87504 _87515 s x f x' t) : term166 _87504 _87515 s x f x' t.
Proof. exact (h1). Qed.
Lemma lem3367882 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term132 _87504 _87515 s x f x' t) = (term132 _87504 _87515 s x f x' t).
Proof. exact (eq_refl (term132 _87504 _87515 s x f x' t)). Qed.
Lemma lem3367911 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term67 _87504 _87515 x f s x' t) = (term67 _87504 _87515 x f s x' t).
Proof. exact (eq_refl (term67 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367912 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term76 _87504 _87515 x f s t) = (term76 _87504 _87515 x f s t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367911 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367913 {_87504 : Type'} : (@all _87504) = (@all _87504).
Proof. exact (eq_refl (@all _87504)). Qed.
Lemma lem3367914 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term77 _87504 _87515 x f s t) = (term77 _87504 _87515 x f s t).
Proof. exact (MK_COMB (@lem3367913 _87504) (@lem3367912 _87504 _87515 x f s t)). Qed.
Lemma lem3367915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3367916 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (t : _87504 -> Prop) : (term93 _87504 _87515 x f s t) = (term93 _87504 _87515 x f s t).
Proof. exact (MK_COMB (@lem3367915) (@lem3367914 _87504 _87515 x f s t)). Qed.
Lemma lem3367917 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term147 _87504 _87515 s x f x' t) = (term147 _87504 _87515 s x f x' t).
Proof. exact (MK_COMB (@lem3367916 _87504 _87515 x f s t) (@lem3367882 _87504 _87515 s x f x' t)). Qed.
Lemma lem3367936 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term79 _87504 _87515 x f x' t) = (term79 _87504 _87515 x f x' t).
Proof. exact (eq_refl (term79 _87504 _87515 x f x' t)). Qed.
Lemma lem3367937 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term85 _87504 _87515 x f t) = (term85 _87504 _87515 x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367936 _87504 _87515 x f x' t)). Qed.
Lemma lem3367938 {_87504 : Type'} : (@all _87504) = (@all _87504).
Proof. exact (eq_refl (@all _87504)). Qed.
Lemma lem3367939 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term86 _87504 _87515 x f t) = (term86 _87504 _87515 x f t).
Proof. exact (MK_COMB (@lem3367938 _87504) (@lem3367937 _87504 _87515 x f t)). Qed.
Lemma lem3367958 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) : (term79 _87504 _87515 x f x' s) = (term79 _87504 _87515 x f x' s).
Proof. exact (eq_refl (term79 _87504 _87515 x f x' s)). Qed.
Lemma lem3367959 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term85 _87504 _87515 x f s) = (term85 _87504 _87515 x f s).
Proof. exact (fun_ext (fun x' : _87504 => @lem3367958 _87504 _87515 x f x' s)). Qed.
Lemma lem3367960 {_87504 : Type'} : (@all _87504) = (@all _87504).
Proof. exact (eq_refl (@all _87504)). Qed.
Lemma lem3367961 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term86 _87504 _87515 x f s) = (term86 _87504 _87515 x f s).
Proof. exact (MK_COMB (@lem3367960 _87504) (@lem3367959 _87504 _87515 x f s)). Qed.
Lemma lem3367962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3367963 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term88 _87504 _87515 x f s) = (term88 _87504 _87515 x f s).
Proof. exact (MK_COMB (@lem3367962) (@lem3367961 _87504 _87515 x f s)). Qed.
Lemma lem3367964 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term90 _87504 _87515 s x f t) = (term90 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3367963 _87504 _87515 x f s) (@lem3367939 _87504 _87515 x f t)). Qed.
Lemma lem3367989 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) (x' : _87504) (t : _87504 -> Prop) : (term113 _87504 _87515 x f s x' t) = (term113 _87504 _87515 x f s x' t).
Proof. exact (eq_refl (term113 _87504 _87515 x f s x' t)). Qed.
Lemma lem3367990 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term115 _87504 _87515 x' s x f t) = (term115 _87504 _87515 x' s x f t).
Proof. exact (MK_COMB (@lem3367989 _87504 _87515 x f s x' t) (@lem3367964 _87504 _87515 s x f t)). Qed.
Lemma lem3367991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3367992 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term164 _87504 _87515 x' s x f t) = (term164 _87504 _87515 x' s x f t).
Proof. exact (MK_COMB (@lem3367991) (@lem3367990 _87504 _87515 x' s x f t)). Qed.
Lemma lem3367993 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term166 _87504 _87515 s x f x' t) = (term166 _87504 _87515 s x f x' t).
Proof. exact (MK_COMB (@lem3367992 _87504 _87515 x' s x f t) (@lem3367917 _87504 _87515 s x f x' t)). Qed.
Lemma lem3367994 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term166 _87504 _87515 s x f x' t) : term166 _87504 _87515 s x f x' t.
Proof. exact (EQ_MP (@lem3367993 _87504 _87515 s x f x' t) (@lem3367849 _87504 _87515 s x f x' t h1)). Qed.
Lemma lem3367995 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term115 _87504 _87515 x' s x f t.
Proof. exact (h1). Qed.
Lemma lem3367996 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) : term147 _87504 _87515 s x f x' t.
Proof. exact (h1). Qed.
Lemma lem3367997 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term90 _87504 _87515 s x f t.
Proof. exact (proj2 (@lem3367995 _87504 _87515 x' s x f t h1)). Qed.
Lemma lem3367998 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term25 _87504 _87515 x f s x' t.
Proof. exact (proj1 (@lem3367995 _87504 _87515 x' s x f t h1)). Qed.
Lemma lem3367999 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term86 _87504 _87515 x f t.
Proof. exact (proj2 (@lem3367997 _87504 _87515 x' s x f t h1)). Qed.
Lemma lem3368000 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term86 _87504 _87515 x f s.
Proof. exact (proj1 (@lem3367997 _87504 _87515 x' s x f t h1)). Qed.
Lemma lem3368001 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term6 _87504 s x' t.
Proof. exact (proj2 (@lem3367998 _87504 _87515 x' s x f t h1)). Qed.
Lemma lem3368005 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) : term132 _87504 _87515 s x f x' t.
Proof. exact (proj2 (@lem3367996 _87504 _87515 s x f x' t h1)). Qed.
Lemma lem3368006 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) : term77 _87504 _87515 x f s t.
Proof. exact (proj1 (@lem3367996 _87504 _87515 s x f x' t h1)). Qed.
Lemma lem3368007 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' s) : term59 _87504 _87515 x f x' s.
Proof. exact (h1). Qed.
Lemma lem3368008 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' t) : term59 _87504 _87515 x f x' t.
Proof. exact (h1). Qed.
Lemma lem3368020 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) : (term79 _87504 _87515 x f x' s) = (term79 _87504 _87515 x f x' s).
Proof. exact (eq_refl (term79 _87504 _87515 x f x' s)). Qed.
Lemma lem3368021 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term85 _87504 _87515 x f s) = (term85 _87504 _87515 x f s).
Proof. exact (fun_ext (fun x' : _87504 => @lem3368020 _87504 _87515 x f x' s)). Qed.
Lemma lem3368022 {_87504 : Type'} : (@all _87504) = (@all _87504).
Proof. exact (eq_refl (@all _87504)). Qed.
Lemma lem3368024 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (s : _87504 -> Prop) : (term86 _87504 _87515 x f s) = (term86 _87504 _87515 x f s).
Proof. exact (MK_COMB (@lem3368022 _87504) (@lem3368021 _87504 _87515 x f s)). Qed.
Lemma lem3368025 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term86 _87504 _87515 x f s.
Proof. exact (EQ_MP (@lem3368024 _87504 _87515 x f s) (@lem3368000 _87504 _87515 x' s x f t h1)). Qed.
Lemma lem3368046 {_87504 : Type'} (x' : _87504) (s : _87504 -> Prop) (h1 : @IN _87504 x' s) : @IN _87504 x' s.
Proof. exact (h1). Qed.
Lemma lem3368067 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term79 _87504 _87515 x f x' t) = (term79 _87504 _87515 x f x' t).
Proof. exact (eq_refl (term79 _87504 _87515 x f x' t)). Qed.
Lemma lem3368068 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term85 _87504 _87515 x f t) = (term85 _87504 _87515 x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3368067 _87504 _87515 x f x' t)). Qed.
Lemma lem3368069 {_87504 : Type'} : (@all _87504) = (@all _87504).
Proof. exact (eq_refl (@all _87504)). Qed.
Lemma lem3368071 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term86 _87504 _87515 x f t) = (term86 _87504 _87515 x f t).
Proof. exact (MK_COMB (@lem3368069 _87504) (@lem3368068 _87504 _87515 x f t)). Qed.
Lemma lem3368072 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term86 _87504 _87515 x f t.
Proof. exact (EQ_MP (@lem3368071 _87504 _87515 x f t) (@lem3367999 _87504 _87515 x' s x f t h1)). Qed.
Lemma lem3368080 {_87504 : Type'} (x' : _87504) (t : _87504 -> Prop) (h1 : @IN _87504 x' t) : @IN _87504 x' t.
Proof. exact (h1). Qed.
Lemma lem3368098 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term67 _87504 _87515 x f s x' t) = (term170 _87504 _87515 s x f x' t).
Proof. exact (@lem19490 (term171 _87504 x' s) (term172 _87504 _87515 x f x') (term171 _87504 x' t)). Qed.
Lemma lem3368099 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term76 _87504 _87515 x f s t) = (term173 _87504 _87515 s x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3368098 _87504 _87515 s x f x' t)). Qed.
Lemma lem3368100 {_87504 : Type'} : (@all _87504) = (@all _87504).
Proof. exact (eq_refl (@all _87504)). Qed.
Lemma lem3368102 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term77 _87504 _87515 x f s t) = (term174 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3368100 _87504) (@lem3368099 _87504 _87515 s x f t)). Qed.
Lemma lem3368103 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) : term174 _87504 _87515 s x f t.
Proof. exact (EQ_MP (@lem3368102 _87504 _87515 s x f t) (@lem3368006 _87504 _87515 s x f x' t h1)). Qed.
Lemma lem3368129 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) : (term67 _87504 _87515 x f s x' t) = (term170 _87504 _87515 s x f x' t).
Proof. exact (@lem19490 (term171 _87504 x' s) (term172 _87504 _87515 x f x') (term171 _87504 x' t)). Qed.
Lemma lem3368130 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term76 _87504 _87515 x f s t) = (term173 _87504 _87515 s x f t).
Proof. exact (fun_ext (fun x' : _87504 => @lem3368129 _87504 _87515 s x f x' t)). Qed.
Lemma lem3368131 {_87504 : Type'} : (@all _87504) = (@all _87504).
Proof. exact (eq_refl (@all _87504)). Qed.
Lemma lem3368133 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term77 _87504 _87515 x f s t) = (term174 _87504 _87515 s x f t).
Proof. exact (MK_COMB (@lem3368131 _87504) (@lem3368130 _87504 _87515 s x f t)). Qed.
Lemma lem3368134 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) : term174 _87504 _87515 s x f t.
Proof. exact (EQ_MP (@lem3368133 _87504 _87515 s x f t) (@lem3368006 _87504 _87515 s x f x' t h1)). Qed.
Lemma lem3368143 {_87504 _87515 : Type'} (_35143 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term175 _87504 _87515 x f s _35143.
Proof. exact (@lem3368025 _87504 _87515 x' s x f t h1 _35143). Qed.
Lemma lem3368144 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) : (term175 _87504 _87515 x f s _35143) = (term79 _87504 _87515 x f _35143 s).
Proof. exact (eq_refl (term175 _87504 _87515 x f s _35143)). Qed.
Lemma lem3368152 {_87504 _87515 : Type'} (_35146 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term175 _87504 _87515 x f t _35146.
Proof. exact (@lem3368072 _87504 _87515 x' s x f t h1 _35146). Qed.
Lemma lem3368153 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) : (term175 _87504 _87515 x f t _35146) = (term79 _87504 _87515 x f _35146 t).
Proof. exact (eq_refl (term175 _87504 _87515 x f t _35146)). Qed.
Lemma lem3368155 {_87504 _87515 : Type'} (_35147 : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) : term176 _87504 _87515 s x f t _35147.
Proof. exact (@lem3368103 _87504 _87515 s x f x' t h1 _35147). Qed.
Lemma lem3368156 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (_35147 : _87504) (t : _87504 -> Prop) : (term176 _87504 _87515 s x f t _35147) = (term170 _87504 _87515 s x f _35147 t).
Proof. exact (eq_refl (term176 _87504 _87515 s x f t _35147)). Qed.
Lemma lem3368157 {_87504 _87515 : Type'} (_35147 : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) : term170 _87504 _87515 s x f _35147 t.
Proof. exact (EQ_MP (@lem3368156 _87504 _87515 s x f _35147 t) (@lem3368155 _87504 _87515 _35147 s x f x' t h1)). Qed.
Lemma lem3368158 {_87504 _87515 : Type'} (_35148 : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) : term176 _87504 _87515 s x f t _35148.
Proof. exact (@lem3368134 _87504 _87515 s x f x' t h1 _35148). Qed.
Lemma lem3368159 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) : (term176 _87504 _87515 s x f t _35148) = (term170 _87504 _87515 s x f _35148 t).
Proof. exact (eq_refl (term176 _87504 _87515 s x f t _35148)). Qed.
Lemma lem3368160 {_87504 _87515 : Type'} (_35148 : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) : term170 _87504 _87515 s x f _35148 t.
Proof. exact (EQ_MP (@lem3368159 _87504 _87515 s x f _35148 t) (@lem3368158 _87504 _87515 _35148 s x f x' t h1)). Qed.
Lemma lem3368170 {_87504 _87515 : Type'} (_35143 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term79 _87504 _87515 x f _35143 s.
Proof. exact (EQ_MP (@lem3368144 _87504 _87515 x f _35143 s) (@lem3368143 _87504 _87515 _35143 x' s x f t h1)). Qed.
Lemma lem3368178 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : x = (f x').
Proof. exact (proj1 (@lem3367998 _87504 _87515 x' s x f t h1)). Qed.
Lemma lem3368180 {_87504 : Type'} (x' : _87504) (s : _87504 -> Prop) (h1 : @IN _87504 x' s) : @IN _87504 x' s.
Proof. exact (h1). Qed.
Lemma lem3368192 {_87504 _87515 : Type'} (_35146 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term79 _87504 _87515 x f _35146 t.
Proof. exact (EQ_MP (@lem3368153 _87504 _87515 x f _35146 t) (@lem3368152 _87504 _87515 _35146 x' s x f t h1)). Qed.
Lemma lem3368194 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : x = (f x').
Proof. exact (proj1 (@lem3367998 _87504 _87515 x' s x f t h1)). Qed.
Lemma lem3368196 {_87504 : Type'} (x' : _87504) (t : _87504 -> Prop) (h1 : @IN _87504 x' t) : @IN _87504 x' t.
Proof. exact (h1). Qed.
Lemma lem3368198 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' s) : x = (f x').
Proof. exact (proj1 (@lem3368007 _87504 _87515 x f x' s h1)). Qed.
Lemma lem3368206 {_87504 _87515 : Type'} (_35147 : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) : term79 _87504 _87515 x f _35147 s.
Proof. exact (proj1 (@lem3368157 _87504 _87515 _35147 s x f x' t h1)). Qed.
Lemma lem3368214 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' t) : x = (f x').
Proof. exact (proj1 (@lem3368008 _87504 _87515 x f x' t h1)). Qed.
Lemma lem3368228 {_87504 _87515 : Type'} (_35148 : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) : term79 _87504 _87515 x f _35148 t.
Proof. exact (proj2 (@lem3368160 _87504 _87515 _35148 s x f x' t h1)). Qed.
Lemma lem3368243 {_87504 _87515 : Type'} (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) : (term177 _87504 _87515 f _35143 s) = (term177 _87504 _87515 f _35143 s).
Proof. exact (eq_refl (term177 _87504 _87515 f _35143 s)). Qed.
Lemma lem3368244 {_87504 _87515 : Type'} (_35143 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : (term178 _87504 _87515 f _35143 s x) = (term179 _87504 _87515 _35143 s f x').
Proof. exact (MK_COMB (@lem3368243 _87504 _87515 f _35143 s) (@lem3368178 _87504 _87515 x' s x f t h1)). Qed.
Lemma lem3368245 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) : (term179 _87504 _87515 _35143 s f x') = (term180 _87504 _87515 x' f _35143 s).
Proof. exact (eq_refl (term179 _87504 _87515 _35143 s f x')). Qed.
Lemma lem3368246 {_87504 _87515 : Type'} (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) (x : _87515) : (term181 _87504 _87515 f _35143 s x) = (term181 _87504 _87515 f _35143 s x).
Proof. exact (eq_refl (term181 _87504 _87515 f _35143 s x)). Qed.
Lemma lem3368247 {_87504 _87515 : Type'} (x : _87515) (x' : _87504) (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) : ((term178 _87504 _87515 f _35143 s x) = (term179 _87504 _87515 _35143 s f x')) = ((term178 _87504 _87515 f _35143 s x) = (term180 _87504 _87515 x' f _35143 s)).
Proof. exact (MK_COMB (@lem3368246 _87504 _87515 f _35143 s x) (@lem3368245 _87504 _87515 x' f _35143 s)). Qed.
Lemma lem3368248 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) : (term178 _87504 _87515 f _35143 s x) = (term79 _87504 _87515 x f _35143 s).
Proof. exact (eq_refl (term178 _87504 _87515 f _35143 s x)). Qed.
Lemma lem3368249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3368250 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) : (term181 _87504 _87515 f _35143 s x) = (term182 _87504 _87515 x f _35143 s).
Proof. exact (MK_COMB (@lem3368249) (@lem3368248 _87504 _87515 x f _35143 s)). Qed.
Lemma lem3368251 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) : (term180 _87504 _87515 x' f _35143 s) = (term180 _87504 _87515 x' f _35143 s).
Proof. exact (eq_refl (term180 _87504 _87515 x' f _35143 s)). Qed.
Lemma lem3368252 {_87504 _87515 : Type'} (x : _87515) (x' : _87504) (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) : ((term178 _87504 _87515 f _35143 s x) = (term180 _87504 _87515 x' f _35143 s)) = ((term79 _87504 _87515 x f _35143 s) = (term180 _87504 _87515 x' f _35143 s)).
Proof. exact (MK_COMB (@lem3368250 _87504 _87515 x f _35143 s) (@lem3368251 _87504 _87515 x' f _35143 s)). Qed.
Lemma lem3368253 {_87504 _87515 : Type'} (x : _87515) (x' : _87504) (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) : ((term178 _87504 _87515 f _35143 s x) = (term179 _87504 _87515 _35143 s f x')) = ((term79 _87504 _87515 x f _35143 s) = (term180 _87504 _87515 x' f _35143 s)).
Proof. exact (TRANS (@lem3368247 _87504 _87515 x x' f _35143 s) (@lem3368252 _87504 _87515 x x' f _35143 s)). Qed.
Lemma lem3368254 {_87504 _87515 : Type'} (_35143 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : (term79 _87504 _87515 x f _35143 s) = (term180 _87504 _87515 x' f _35143 s).
Proof. exact (EQ_MP (@lem3368253 _87504 _87515 x x' f _35143 s) (@lem3368244 _87504 _87515 _35143 x' s x f t h1)). Qed.
Lemma lem3368255 {_87504 _87515 : Type'} (_35143 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term180 _87504 _87515 x' f _35143 s.
Proof. exact (EQ_MP (@lem3368254 _87504 _87515 _35143 x' s x f t h1) (@lem3368170 _87504 _87515 _35143 x' s x f t h1)). Qed.
Lemma lem3368282 {_87504 : Type'} (x' : _87504) (s : _87504 -> Prop) (h1 : @IN _87504 x' s) : @IN _87504 x' s.
Proof. exact (h1). Qed.
Lemma lem3368310 {_87504 _87515 : Type'} (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) : (term177 _87504 _87515 f _35146 t) = (term177 _87504 _87515 f _35146 t).
Proof. exact (eq_refl (term177 _87504 _87515 f _35146 t)). Qed.
Lemma lem3368311 {_87504 _87515 : Type'} (_35146 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : (term178 _87504 _87515 f _35146 t x) = (term179 _87504 _87515 _35146 t f x').
Proof. exact (MK_COMB (@lem3368310 _87504 _87515 f _35146 t) (@lem3368194 _87504 _87515 x' s x f t h1)). Qed.
Lemma lem3368312 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) : (term179 _87504 _87515 _35146 t f x') = (term180 _87504 _87515 x' f _35146 t).
Proof. exact (eq_refl (term179 _87504 _87515 _35146 t f x')). Qed.
Lemma lem3368313 {_87504 _87515 : Type'} (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) (x : _87515) : (term181 _87504 _87515 f _35146 t x) = (term181 _87504 _87515 f _35146 t x).
Proof. exact (eq_refl (term181 _87504 _87515 f _35146 t x)). Qed.
Lemma lem3368314 {_87504 _87515 : Type'} (x : _87515) (x' : _87504) (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) : ((term178 _87504 _87515 f _35146 t x) = (term179 _87504 _87515 _35146 t f x')) = ((term178 _87504 _87515 f _35146 t x) = (term180 _87504 _87515 x' f _35146 t)).
Proof. exact (MK_COMB (@lem3368313 _87504 _87515 f _35146 t x) (@lem3368312 _87504 _87515 x' f _35146 t)). Qed.
Lemma lem3368315 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) : (term178 _87504 _87515 f _35146 t x) = (term79 _87504 _87515 x f _35146 t).
Proof. exact (eq_refl (term178 _87504 _87515 f _35146 t x)). Qed.
Lemma lem3368316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3368317 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) : (term181 _87504 _87515 f _35146 t x) = (term182 _87504 _87515 x f _35146 t).
Proof. exact (MK_COMB (@lem3368316) (@lem3368315 _87504 _87515 x f _35146 t)). Qed.
Lemma lem3368318 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) : (term180 _87504 _87515 x' f _35146 t) = (term180 _87504 _87515 x' f _35146 t).
Proof. exact (eq_refl (term180 _87504 _87515 x' f _35146 t)). Qed.
Lemma lem3368319 {_87504 _87515 : Type'} (x : _87515) (x' : _87504) (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) : ((term178 _87504 _87515 f _35146 t x) = (term180 _87504 _87515 x' f _35146 t)) = ((term79 _87504 _87515 x f _35146 t) = (term180 _87504 _87515 x' f _35146 t)).
Proof. exact (MK_COMB (@lem3368317 _87504 _87515 x f _35146 t) (@lem3368318 _87504 _87515 x' f _35146 t)). Qed.
Lemma lem3368320 {_87504 _87515 : Type'} (x : _87515) (x' : _87504) (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) : ((term178 _87504 _87515 f _35146 t x) = (term179 _87504 _87515 _35146 t f x')) = ((term79 _87504 _87515 x f _35146 t) = (term180 _87504 _87515 x' f _35146 t)).
Proof. exact (TRANS (@lem3368314 _87504 _87515 x x' f _35146 t) (@lem3368319 _87504 _87515 x x' f _35146 t)). Qed.
Lemma lem3368321 {_87504 _87515 : Type'} (_35146 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : (term79 _87504 _87515 x f _35146 t) = (term180 _87504 _87515 x' f _35146 t).
Proof. exact (EQ_MP (@lem3368320 _87504 _87515 x x' f _35146 t) (@lem3368311 _87504 _87515 _35146 x' s x f t h1)). Qed.
Lemma lem3368322 {_87504 _87515 : Type'} (_35146 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term180 _87504 _87515 x' f _35146 t.
Proof. exact (EQ_MP (@lem3368321 _87504 _87515 _35146 x' s x f t h1) (@lem3368192 _87504 _87515 _35146 x' s x f t h1)). Qed.
Lemma lem3368336 {_87504 : Type'} (x' : _87504) (t : _87504 -> Prop) (h1 : @IN _87504 x' t) : @IN _87504 x' t.
Proof. exact (h1). Qed.
Lemma lem3368365 {_87504 _87515 : Type'} (f : _87504 -> _87515) (_35147 : _87504) (s : _87504 -> Prop) : (term177 _87504 _87515 f _35147 s) = (term177 _87504 _87515 f _35147 s).
Proof. exact (eq_refl (term177 _87504 _87515 f _35147 s)). Qed.
Lemma lem3368366 {_87504 _87515 : Type'} (_35147 : _87504) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' s) : (term178 _87504 _87515 f _35147 s x) = (term179 _87504 _87515 _35147 s f x').
Proof. exact (MK_COMB (@lem3368365 _87504 _87515 f _35147 s) (@lem3368198 _87504 _87515 x f x' s h1)). Qed.
Lemma lem3368367 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35147 : _87504) (s : _87504 -> Prop) : (term179 _87504 _87515 _35147 s f x') = (term180 _87504 _87515 x' f _35147 s).
Proof. exact (eq_refl (term179 _87504 _87515 _35147 s f x')). Qed.
Lemma lem3368368 {_87504 _87515 : Type'} (f : _87504 -> _87515) (_35147 : _87504) (s : _87504 -> Prop) (x : _87515) : (term181 _87504 _87515 f _35147 s x) = (term181 _87504 _87515 f _35147 s x).
Proof. exact (eq_refl (term181 _87504 _87515 f _35147 s x)). Qed.
Lemma lem3368369 {_87504 _87515 : Type'} (x : _87515) (x' : _87504) (f : _87504 -> _87515) (_35147 : _87504) (s : _87504 -> Prop) : ((term178 _87504 _87515 f _35147 s x) = (term179 _87504 _87515 _35147 s f x')) = ((term178 _87504 _87515 f _35147 s x) = (term180 _87504 _87515 x' f _35147 s)).
Proof. exact (MK_COMB (@lem3368368 _87504 _87515 f _35147 s x) (@lem3368367 _87504 _87515 x' f _35147 s)). Qed.
Lemma lem3368370 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (_35147 : _87504) (s : _87504 -> Prop) : (term178 _87504 _87515 f _35147 s x) = (term79 _87504 _87515 x f _35147 s).
Proof. exact (eq_refl (term178 _87504 _87515 f _35147 s x)). Qed.
Lemma lem3368371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3368372 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (_35147 : _87504) (s : _87504 -> Prop) : (term181 _87504 _87515 f _35147 s x) = (term182 _87504 _87515 x f _35147 s).
Proof. exact (MK_COMB (@lem3368371) (@lem3368370 _87504 _87515 x f _35147 s)). Qed.
Lemma lem3368373 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35147 : _87504) (s : _87504 -> Prop) : (term180 _87504 _87515 x' f _35147 s) = (term180 _87504 _87515 x' f _35147 s).
Proof. exact (eq_refl (term180 _87504 _87515 x' f _35147 s)). Qed.
Lemma lem3368374 {_87504 _87515 : Type'} (x : _87515) (x' : _87504) (f : _87504 -> _87515) (_35147 : _87504) (s : _87504 -> Prop) : ((term178 _87504 _87515 f _35147 s x) = (term180 _87504 _87515 x' f _35147 s)) = ((term79 _87504 _87515 x f _35147 s) = (term180 _87504 _87515 x' f _35147 s)).
Proof. exact (MK_COMB (@lem3368372 _87504 _87515 x f _35147 s) (@lem3368373 _87504 _87515 x' f _35147 s)). Qed.
Lemma lem3368375 {_87504 _87515 : Type'} (x : _87515) (x' : _87504) (f : _87504 -> _87515) (_35147 : _87504) (s : _87504 -> Prop) : ((term178 _87504 _87515 f _35147 s x) = (term179 _87504 _87515 _35147 s f x')) = ((term79 _87504 _87515 x f _35147 s) = (term180 _87504 _87515 x' f _35147 s)).
Proof. exact (TRANS (@lem3368369 _87504 _87515 x x' f _35147 s) (@lem3368374 _87504 _87515 x x' f _35147 s)). Qed.
Lemma lem3368376 {_87504 _87515 : Type'} (_35147 : _87504) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' s) : (term79 _87504 _87515 x f _35147 s) = (term180 _87504 _87515 x' f _35147 s).
Proof. exact (EQ_MP (@lem3368375 _87504 _87515 x x' f _35147 s) (@lem3368366 _87504 _87515 _35147 x f x' s h1)). Qed.
Lemma lem3368377 {_87504 _87515 : Type'} (_35147 : _87504) (t : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' s) : term180 _87504 _87515 x' f _35147 s.
Proof. exact (EQ_MP (@lem3368376 _87504 _87515 _35147 x f x' s h2) (@lem3368206 _87504 _87515 _35147 s x f x' t h1)). Qed.
Lemma lem3368432 {_87504 _87515 : Type'} (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) : (term177 _87504 _87515 f _35148 t) = (term177 _87504 _87515 f _35148 t).
Proof. exact (eq_refl (term177 _87504 _87515 f _35148 t)). Qed.
Lemma lem3368433 {_87504 _87515 : Type'} (_35148 : _87504) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' t) : (term178 _87504 _87515 f _35148 t x) = (term179 _87504 _87515 _35148 t f x').
Proof. exact (MK_COMB (@lem3368432 _87504 _87515 f _35148 t) (@lem3368214 _87504 _87515 x f x' t h1)). Qed.
Lemma lem3368434 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) : (term179 _87504 _87515 _35148 t f x') = (term180 _87504 _87515 x' f _35148 t).
Proof. exact (eq_refl (term179 _87504 _87515 _35148 t f x')). Qed.
Lemma lem3368435 {_87504 _87515 : Type'} (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) (x : _87515) : (term181 _87504 _87515 f _35148 t x) = (term181 _87504 _87515 f _35148 t x).
Proof. exact (eq_refl (term181 _87504 _87515 f _35148 t x)). Qed.
Lemma lem3368436 {_87504 _87515 : Type'} (x : _87515) (x' : _87504) (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) : ((term178 _87504 _87515 f _35148 t x) = (term179 _87504 _87515 _35148 t f x')) = ((term178 _87504 _87515 f _35148 t x) = (term180 _87504 _87515 x' f _35148 t)).
Proof. exact (MK_COMB (@lem3368435 _87504 _87515 f _35148 t x) (@lem3368434 _87504 _87515 x' f _35148 t)). Qed.
Lemma lem3368437 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) : (term178 _87504 _87515 f _35148 t x) = (term79 _87504 _87515 x f _35148 t).
Proof. exact (eq_refl (term178 _87504 _87515 f _35148 t x)). Qed.
Lemma lem3368438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3368439 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) : (term181 _87504 _87515 f _35148 t x) = (term182 _87504 _87515 x f _35148 t).
Proof. exact (MK_COMB (@lem3368438) (@lem3368437 _87504 _87515 x f _35148 t)). Qed.
Lemma lem3368440 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) : (term180 _87504 _87515 x' f _35148 t) = (term180 _87504 _87515 x' f _35148 t).
Proof. exact (eq_refl (term180 _87504 _87515 x' f _35148 t)). Qed.
Lemma lem3368441 {_87504 _87515 : Type'} (x : _87515) (x' : _87504) (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) : ((term178 _87504 _87515 f _35148 t x) = (term180 _87504 _87515 x' f _35148 t)) = ((term79 _87504 _87515 x f _35148 t) = (term180 _87504 _87515 x' f _35148 t)).
Proof. exact (MK_COMB (@lem3368439 _87504 _87515 x f _35148 t) (@lem3368440 _87504 _87515 x' f _35148 t)). Qed.
Lemma lem3368442 {_87504 _87515 : Type'} (x : _87515) (x' : _87504) (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) : ((term178 _87504 _87515 f _35148 t x) = (term179 _87504 _87515 _35148 t f x')) = ((term79 _87504 _87515 x f _35148 t) = (term180 _87504 _87515 x' f _35148 t)).
Proof. exact (TRANS (@lem3368436 _87504 _87515 x x' f _35148 t) (@lem3368441 _87504 _87515 x x' f _35148 t)). Qed.
Lemma lem3368443 {_87504 _87515 : Type'} (_35148 : _87504) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' t) : (term79 _87504 _87515 x f _35148 t) = (term180 _87504 _87515 x' f _35148 t).
Proof. exact (EQ_MP (@lem3368442 _87504 _87515 x x' f _35148 t) (@lem3368433 _87504 _87515 _35148 x f x' t h1)). Qed.
Lemma lem3368444 {_87504 _87515 : Type'} (_35148 : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' t) : term180 _87504 _87515 x' f _35148 t.
Proof. exact (EQ_MP (@lem3368443 _87504 _87515 _35148 x f x' t h2) (@lem3368228 _87504 _87515 _35148 s x f x' t h1)). Qed.
Lemma lem3368479 {_87515 : Type'} (x : _87515) : x = x.
Proof. exact (@lem21386 _87515 x). Qed.
Lemma lem3368480 {_87515 : Type'} (x : _87515) : x = x.
Proof. exact (@lem3368479 _87515 x). Qed.
Lemma lem3368481 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : (f x') = (f x').
Proof. exact (@lem3368480 _87515 (f x')). Qed.
Lemma lem3368482 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : term183 _87504 _87515 f x'.
Proof. exact (fun h0 : term184 _87504 _87515 f x' => @lem3368481 _87504 _87515 f x'). Qed.
Lemma lem3368484 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3368485 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : (term183 _87504 _87515 f x') = ((f x') = (f x')).
Proof. exact (@lem3368484 ((f x') = (f x'))). Qed.
Lemma lem3368486 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3368485 _87504 _87515 f x') (@lem3368482 _87504 _87515 f x')). Qed.
Lemma lem3368488 {_87504 : Type'} (x' : _87504) (s : _87504 -> Prop) (h1 : @IN _87504 x' s) : @IN _87504 x' s.
Proof. exact (h1). Qed.
Lemma lem3368489 {_87504 : Type'} (x' : _87504) (s : _87504 -> Prop) (h1 : @IN _87504 x' s) : term186 _87504 x' s.
Proof. exact (fun h0 : term171 _87504 x' s => @lem3368488 _87504 x' s h1). Qed.
Lemma lem3368491 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3368492 {_87504 : Type'} (x' : _87504) (s : _87504 -> Prop) : (term186 _87504 x' s) = (@IN _87504 x' s).
Proof. exact (@lem3368491 (@IN _87504 x' s)). Qed.
Lemma lem3368493 {_87504 : Type'} (x' : _87504) (s : _87504 -> Prop) (h1 : @IN _87504 x' s) : @IN _87504 x' s.
Proof. exact (EQ_MP (@lem3368492 _87504 x' s) (@lem3368489 _87504 x' s h1)). Qed.
Lemma lem3368495 (a : Prop) (b : Prop) : (term187 a b) = (term188 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3368496 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) : (term180 _87504 _87515 x' f _35143 s) = (term189 _87504 _87515 x' f _35143 s).
Proof. exact (@lem3368495 ((f x') = (f _35143)) (@IN _87504 _35143 s)). Qed.
Lemma lem3368498 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3368499 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) : (term189 _87504 _87515 x' f _35143 s) = (term190 _87504 _87515 x' f _35143 s).
Proof. exact (@lem3368498 (term191 _87504 _87515 x' f _35143 s)). Qed.
Lemma lem3368500 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35143 : _87504) (s : _87504 -> Prop) : (term180 _87504 _87515 x' f _35143 s) = (term190 _87504 _87515 x' f _35143 s).
Proof. exact (TRANS (@lem3368496 _87504 _87515 x' f _35143 s) (@lem3368499 _87504 _87515 x' f _35143 s)). Qed.
Lemma lem3368502 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : @IN _87504 x' s) : term192 _87504 _87515 f x' s.
Proof. exact (conj (@lem3368486 _87504 _87515 f x') (@lem3368493 _87504 x' s h1)). Qed.
Lemma lem3368504 {_87504 _87515 : Type'} (_35143 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term190 _87504 _87515 x' f _35143 s.
Proof. exact (EQ_MP (@lem3368500 _87504 _87515 x' f _35143 s) (@lem3368255 _87504 _87515 _35143 x' s x f t h1)). Qed.
Lemma lem3368505 {_87504 _87515 : Type'} (_35143 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term190 _87504 _87515 x' f _35143 s.
Proof. exact (@lem3368504 _87504 _87515 _35143 x' s x f t h1). Qed.
Lemma lem3368506 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term193 _87504 _87515 f x' s.
Proof. exact (@lem3368505 _87504 _87515 x' x' s x f t h1). Qed.
Lemma lem3368509 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (x' : _87504) (s : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' s) : False.
Proof. exact (@lem3368506 _87504 _87515 x' s x f t h1 (@lem3368502 _87504 _87515 f x' s h2)). Qed.
Lemma lem3368510 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (x' : _87504) (s : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' s) : term194.
Proof. exact (fun h0 : ~ False => @lem3368509 _87504 _87515 x f t x' s h1 h2). Qed.
Lemma lem3368512 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3368513 : term194 = False.
Proof. exact (@lem3368512 False). Qed.
Lemma lem3368514 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (x' : _87504) (s : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' s) : False.
Proof. exact (EQ_MP (@lem3368513) (@lem3368510 _87504 _87515 x f t x' s h1 h2)). Qed.
Lemma lem3368549 {_87515 : Type'} (x : _87515) : x = x.
Proof. exact (@lem21386 _87515 x). Qed.
Lemma lem3368550 {_87515 : Type'} (x : _87515) : x = x.
Proof. exact (@lem3368549 _87515 x). Qed.
Lemma lem3368551 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : (f x') = (f x').
Proof. exact (@lem3368550 _87515 (f x')). Qed.
Lemma lem3368552 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : term183 _87504 _87515 f x'.
Proof. exact (fun h0 : term184 _87504 _87515 f x' => @lem3368551 _87504 _87515 f x'). Qed.
Lemma lem3368554 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3368555 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : (term183 _87504 _87515 f x') = ((f x') = (f x')).
Proof. exact (@lem3368554 ((f x') = (f x'))). Qed.
Lemma lem3368556 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3368555 _87504 _87515 f x') (@lem3368552 _87504 _87515 f x')). Qed.
Lemma lem3368558 {_87504 : Type'} (x' : _87504) (t : _87504 -> Prop) (h1 : @IN _87504 x' t) : @IN _87504 x' t.
Proof. exact (h1). Qed.
Lemma lem3368559 {_87504 : Type'} (x' : _87504) (t : _87504 -> Prop) (h1 : @IN _87504 x' t) : term186 _87504 x' t.
Proof. exact (fun h0 : term171 _87504 x' t => @lem3368558 _87504 x' t h1). Qed.
Lemma lem3368561 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3368562 {_87504 : Type'} (x' : _87504) (t : _87504 -> Prop) : (term186 _87504 x' t) = (@IN _87504 x' t).
Proof. exact (@lem3368561 (@IN _87504 x' t)). Qed.
Lemma lem3368563 {_87504 : Type'} (x' : _87504) (t : _87504 -> Prop) (h1 : @IN _87504 x' t) : @IN _87504 x' t.
Proof. exact (EQ_MP (@lem3368562 _87504 x' t) (@lem3368559 _87504 x' t h1)). Qed.
Lemma lem3368565 (a : Prop) (b : Prop) : (term187 a b) = (term188 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3368566 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) : (term180 _87504 _87515 x' f _35146 t) = (term189 _87504 _87515 x' f _35146 t).
Proof. exact (@lem3368565 ((f x') = (f _35146)) (@IN _87504 _35146 t)). Qed.
Lemma lem3368568 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3368569 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) : (term189 _87504 _87515 x' f _35146 t) = (term190 _87504 _87515 x' f _35146 t).
Proof. exact (@lem3368568 (term191 _87504 _87515 x' f _35146 t)). Qed.
Lemma lem3368570 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35146 : _87504) (t : _87504 -> Prop) : (term180 _87504 _87515 x' f _35146 t) = (term190 _87504 _87515 x' f _35146 t).
Proof. exact (TRANS (@lem3368566 _87504 _87515 x' f _35146 t) (@lem3368569 _87504 _87515 x' f _35146 t)). Qed.
Lemma lem3368572 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : @IN _87504 x' t) : term192 _87504 _87515 f x' t.
Proof. exact (conj (@lem3368556 _87504 _87515 f x') (@lem3368563 _87504 x' t h1)). Qed.
Lemma lem3368574 {_87504 _87515 : Type'} (_35146 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term190 _87504 _87515 x' f _35146 t.
Proof. exact (EQ_MP (@lem3368570 _87504 _87515 x' f _35146 t) (@lem3368322 _87504 _87515 _35146 x' s x f t h1)). Qed.
Lemma lem3368575 {_87504 _87515 : Type'} (_35146 : _87504) (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term190 _87504 _87515 x' f _35146 t.
Proof. exact (@lem3368574 _87504 _87515 _35146 x' s x f t h1). Qed.
Lemma lem3368576 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : term193 _87504 _87515 f x' t.
Proof. exact (@lem3368575 _87504 _87515 x' x' s x f t h1). Qed.
Lemma lem3368579 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' t) : False.
Proof. exact (@lem3368576 _87504 _87515 x' s x f t h1 (@lem3368572 _87504 _87515 f x' t h2)). Qed.
Lemma lem3368580 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' t) : term194.
Proof. exact (fun h0 : ~ False => @lem3368579 _87504 _87515 s x f x' t h1 h2). Qed.
Lemma lem3368582 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3368583 : term194 = False.
Proof. exact (@lem3368582 False). Qed.
Lemma lem3368584 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' t) : False.
Proof. exact (EQ_MP (@lem3368583) (@lem3368580 _87504 _87515 s x f x' t h1 h2)). Qed.
Lemma lem3368619 {_87515 : Type'} (x : _87515) : x = x.
Proof. exact (@lem21386 _87515 x). Qed.
Lemma lem3368620 {_87515 : Type'} (x : _87515) : x = x.
Proof. exact (@lem3368619 _87515 x). Qed.
Lemma lem3368621 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : (f x') = (f x').
Proof. exact (@lem3368620 _87515 (f x')). Qed.
Lemma lem3368622 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : term183 _87504 _87515 f x'.
Proof. exact (fun h0 : term184 _87504 _87515 f x' => @lem3368621 _87504 _87515 f x'). Qed.
Lemma lem3368624 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3368625 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : (term183 _87504 _87515 f x') = ((f x') = (f x')).
Proof. exact (@lem3368624 ((f x') = (f x'))). Qed.
Lemma lem3368626 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3368625 _87504 _87515 f x') (@lem3368622 _87504 _87515 f x')). Qed.
Lemma lem3368628 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' s) : @IN _87504 x' s.
Proof. exact (proj2 (@lem3368007 _87504 _87515 x f x' s h1)). Qed.
Lemma lem3368629 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' s) : term186 _87504 x' s.
Proof. exact (fun h0 : term171 _87504 x' s => @lem3368628 _87504 _87515 x f x' s h1). Qed.
Lemma lem3368631 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3368632 {_87504 : Type'} (x' : _87504) (s : _87504 -> Prop) : (term186 _87504 x' s) = (@IN _87504 x' s).
Proof. exact (@lem3368631 (@IN _87504 x' s)). Qed.
Lemma lem3368633 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' s) : @IN _87504 x' s.
Proof. exact (EQ_MP (@lem3368632 _87504 x' s) (@lem3368629 _87504 _87515 x f x' s h1)). Qed.
Lemma lem3368635 (a : Prop) (b : Prop) : (term187 a b) = (term188 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3368636 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35147 : _87504) (s : _87504 -> Prop) : (term180 _87504 _87515 x' f _35147 s) = (term189 _87504 _87515 x' f _35147 s).
Proof. exact (@lem3368635 ((f x') = (f _35147)) (@IN _87504 _35147 s)). Qed.
Lemma lem3368638 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3368639 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35147 : _87504) (s : _87504 -> Prop) : (term189 _87504 _87515 x' f _35147 s) = (term190 _87504 _87515 x' f _35147 s).
Proof. exact (@lem3368638 (term191 _87504 _87515 x' f _35147 s)). Qed.
Lemma lem3368640 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35147 : _87504) (s : _87504 -> Prop) : (term180 _87504 _87515 x' f _35147 s) = (term190 _87504 _87515 x' f _35147 s).
Proof. exact (TRANS (@lem3368636 _87504 _87515 x' f _35147 s) (@lem3368639 _87504 _87515 x' f _35147 s)). Qed.
Lemma lem3368642 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' s) : term192 _87504 _87515 f x' s.
Proof. exact (conj (@lem3368626 _87504 _87515 f x') (@lem3368633 _87504 _87515 x f x' s h1)). Qed.
Lemma lem3368644 {_87504 _87515 : Type'} (_35147 : _87504) (t : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' s) : term190 _87504 _87515 x' f _35147 s.
Proof. exact (EQ_MP (@lem3368640 _87504 _87515 x' f _35147 s) (@lem3368377 _87504 _87515 _35147 t x f x' s h1 h2)). Qed.
Lemma lem3368645 {_87504 _87515 : Type'} (_35147 : _87504) (t : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' s) : term190 _87504 _87515 x' f _35147 s.
Proof. exact (@lem3368644 _87504 _87515 _35147 t x f x' s h1 h2). Qed.
Lemma lem3368646 {_87504 _87515 : Type'} (t : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' s) : term193 _87504 _87515 f x' s.
Proof. exact (@lem3368645 _87504 _87515 x' t x f x' s h1 h2). Qed.
Lemma lem3368649 {_87504 _87515 : Type'} (t : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' s) : False.
Proof. exact (@lem3368646 _87504 _87515 t x f x' s h1 h2 (@lem3368642 _87504 _87515 x f x' s h2)). Qed.
Lemma lem3368650 {_87504 _87515 : Type'} (t : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' s) : term194.
Proof. exact (fun h0 : ~ False => @lem3368649 _87504 _87515 t x f x' s h1 h2). Qed.
Lemma lem3368652 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3368653 : term194 = False.
Proof. exact (@lem3368652 False). Qed.
Lemma lem3368689 {_87515 : Type'} (x : _87515) : x = x.
Proof. exact (@lem21386 _87515 x). Qed.
Lemma lem3368690 {_87515 : Type'} (x : _87515) : x = x.
Proof. exact (@lem3368689 _87515 x). Qed.
Lemma lem3368691 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : (f x') = (f x').
Proof. exact (@lem3368690 _87515 (f x')). Qed.
Lemma lem3368692 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : term183 _87504 _87515 f x'.
Proof. exact (fun h0 : term184 _87504 _87515 f x' => @lem3368691 _87504 _87515 f x'). Qed.
Lemma lem3368694 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3368695 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : (term183 _87504 _87515 f x') = ((f x') = (f x')).
Proof. exact (@lem3368694 ((f x') = (f x'))). Qed.
Lemma lem3368696 {_87504 _87515 : Type'} (f : _87504 -> _87515) (x' : _87504) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3368695 _87504 _87515 f x') (@lem3368692 _87504 _87515 f x')). Qed.
Lemma lem3368698 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' t) : @IN _87504 x' t.
Proof. exact (proj2 (@lem3368008 _87504 _87515 x f x' t h1)). Qed.
Lemma lem3368699 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' t) : term186 _87504 x' t.
Proof. exact (fun h0 : term171 _87504 x' t => @lem3368698 _87504 _87515 x f x' t h1). Qed.
Lemma lem3368701 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3368702 {_87504 : Type'} (x' : _87504) (t : _87504 -> Prop) : (term186 _87504 x' t) = (@IN _87504 x' t).
Proof. exact (@lem3368701 (@IN _87504 x' t)). Qed.
Lemma lem3368703 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' t) : @IN _87504 x' t.
Proof. exact (EQ_MP (@lem3368702 _87504 x' t) (@lem3368699 _87504 _87515 x f x' t h1)). Qed.
Lemma lem3368705 (a : Prop) (b : Prop) : (term187 a b) = (term188 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3368706 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) : (term180 _87504 _87515 x' f _35148 t) = (term189 _87504 _87515 x' f _35148 t).
Proof. exact (@lem3368705 ((f x') = (f _35148)) (@IN _87504 _35148 t)). Qed.
Lemma lem3368708 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3368709 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) : (term189 _87504 _87515 x' f _35148 t) = (term190 _87504 _87515 x' f _35148 t).
Proof. exact (@lem3368708 (term191 _87504 _87515 x' f _35148 t)). Qed.
Lemma lem3368710 {_87504 _87515 : Type'} (x' : _87504) (f : _87504 -> _87515) (_35148 : _87504) (t : _87504 -> Prop) : (term180 _87504 _87515 x' f _35148 t) = (term190 _87504 _87515 x' f _35148 t).
Proof. exact (TRANS (@lem3368706 _87504 _87515 x' f _35148 t) (@lem3368709 _87504 _87515 x' f _35148 t)). Qed.
Lemma lem3368712 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term59 _87504 _87515 x f x' t) : term192 _87504 _87515 f x' t.
Proof. exact (conj (@lem3368696 _87504 _87515 f x') (@lem3368703 _87504 _87515 x f x' t h1)). Qed.
Lemma lem3368714 {_87504 _87515 : Type'} (_35148 : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' t) : term190 _87504 _87515 x' f _35148 t.
Proof. exact (EQ_MP (@lem3368710 _87504 _87515 x' f _35148 t) (@lem3368444 _87504 _87515 _35148 s x f x' t h1 h2)). Qed.
Lemma lem3368715 {_87504 _87515 : Type'} (_35148 : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' t) : term190 _87504 _87515 x' f _35148 t.
Proof. exact (@lem3368714 _87504 _87515 _35148 s x f x' t h1 h2). Qed.
Lemma lem3368716 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' t) : term193 _87504 _87515 f x' t.
Proof. exact (@lem3368715 _87504 _87515 x' s x f x' t h1 h2). Qed.
Lemma lem3368719 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' t) : False.
Proof. exact (@lem3368716 _87504 _87515 s x f x' t h1 h2 (@lem3368712 _87504 _87515 x f x' t h2)). Qed.
Lemma lem3368720 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' t) : term194.
Proof. exact (fun h0 : ~ False => @lem3368719 _87504 _87515 s x f x' t h1 h2). Qed.
Lemma lem3368722 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3368723 : term194 = False.
Proof. exact (@lem3368722 False). Qed.
Lemma lem3368725 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' t) : False.
Proof. exact (EQ_MP (@lem3368723) (@lem3368720 _87504 _87515 s x f x' t h1 h2)). Qed.
Lemma lem3368726 {_87504 _87515 : Type'} (t : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (s : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) (h2 : term59 _87504 _87515 x f x' s) : False.
Proof. exact (EQ_MP (@lem3368653) (@lem3368650 _87504 _87515 t x f x' s h1 h2)). Qed.
Lemma lem3368727 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' t) : (@IN _87504 x' t) = False.
Proof. exact (prop_ext (fun h3 : @IN _87504 x' t => @lem3368584 _87504 _87515 s x f x' t h1 h2) (fun h3 : False => @lem3368336 _87504 x' t h2)). Qed.
Lemma lem3368729 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' t) : False.
Proof. exact (EQ_MP (@lem3368727 _87504 _87515 s x f x' t h1 h2) (@lem3368336 _87504 x' t h2)). Qed.
Lemma lem3368730 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (x' : _87504) (s : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' s) : (@IN _87504 x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _87504 x' s => @lem3368514 _87504 _87515 x f t x' s h1 h2) (fun h3 : False => @lem3368282 _87504 x' s h2)). Qed.
Lemma lem3368732 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (x' : _87504) (s : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' s) : False.
Proof. exact (EQ_MP (@lem3368730 _87504 _87515 x f t x' s h1 h2) (@lem3368282 _87504 x' s h2)). Qed.
Lemma lem3368733 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' t) : (@IN _87504 x' t) = False.
Proof. exact (prop_ext (fun h3 : @IN _87504 x' t => @lem3368729 _87504 _87515 s x f x' t h1 h2) (fun h3 : False => @lem3368196 _87504 x' t h2)). Qed.
Lemma lem3368734 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' t) : False.
Proof. exact (EQ_MP (@lem3368733 _87504 _87515 s x f x' t h1 h2) (@lem3368196 _87504 x' t h2)). Qed.
Lemma lem3368735 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (x' : _87504) (s : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' s) : (@IN _87504 x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _87504 x' s => @lem3368732 _87504 _87515 x f t x' s h1 h2) (fun h3 : False => @lem3368180 _87504 x' s h2)). Qed.
Lemma lem3368736 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (x' : _87504) (s : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' s) : False.
Proof. exact (EQ_MP (@lem3368735 _87504 _87515 x f t x' s h1 h2) (@lem3368180 _87504 x' s h2)). Qed.
Lemma lem3368737 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' t) : (@IN _87504 x' t) = False.
Proof. exact (prop_ext (fun h3 : @IN _87504 x' t => @lem3368734 _87504 _87515 s x f x' t h1 h2) (fun h3 : False => @lem3368080 _87504 x' t h2)). Qed.
Lemma lem3368738 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' t) : False.
Proof. exact (EQ_MP (@lem3368737 _87504 _87515 s x f x' t h1 h2) (@lem3368080 _87504 x' t h2)). Qed.
Lemma lem3368739 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (x' : _87504) (s : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' s) : (@IN _87504 x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _87504 x' s => @lem3368736 _87504 _87515 x f t x' s h1 h2) (fun h3 : False => @lem3368046 _87504 x' s h2)). Qed.
Lemma lem3368740 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (x' : _87504) (s : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' s) : False.
Proof. exact (EQ_MP (@lem3368739 _87504 _87515 x f t x' s h1 h2) (@lem3368046 _87504 x' s h2)). Qed.
Lemma lem3368741 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' t) : (@IN _87504 x' t) = False.
Proof. exact (prop_ext (fun h3 : @IN _87504 x' t => @lem3368738 _87504 _87515 s x f x' t h1 h2) (fun h3 : False => @lem3368080 _87504 x' t h2)). Qed.
Lemma lem3368742 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' t) : False.
Proof. exact (EQ_MP (@lem3368741 _87504 _87515 s x f x' t h1 h2) (@lem3368080 _87504 x' t h2)). Qed.
Lemma lem3368743 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (x' : _87504) (s : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' s) : (@IN _87504 x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN _87504 x' s => @lem3368740 _87504 _87515 x f t x' s h1 h2) (fun h3 : False => @lem3368046 _87504 x' s h2)). Qed.
Lemma lem3368744 {_87504 _87515 : Type'} (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (x' : _87504) (s : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) (h2 : @IN _87504 x' s) : False.
Proof. exact (EQ_MP (@lem3368743 _87504 _87515 x f t x' s h1 h2) (@lem3368046 _87504 x' s h2)). Qed.
Lemma lem3368745 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term147 _87504 _87515 s x f x' t) : False.
Proof. exact (or_elim (@lem3368005 _87504 _87515 s x f x' t h1) (fun h0 : term59 _87504 _87515 x f x' s => @lem3368726 _87504 _87515 t x f x' s h1 h0) (fun h0 : term59 _87504 _87515 x f x' t => @lem3368725 _87504 _87515 s x f x' t h1 h0)). Qed.
Lemma lem3368746 {_87504 _87515 : Type'} (x' : _87504) (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term115 _87504 _87515 x' s x f t) : False.
Proof. exact (or_elim (@lem3368001 _87504 _87515 x' s x f t h1) (fun h0 : @IN _87504 x' s => @lem3368744 _87504 _87515 x f t x' s h1 h0) (fun h0 : @IN _87504 x' t => @lem3368742 _87504 _87515 s x f x' t h1 h0)). Qed.
Lemma lem3368747 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term166 _87504 _87515 s x f x' t) : False.
Proof. exact (or_elim (@lem3367994 _87504 _87515 s x f x' t h1) (fun h0 : term115 _87504 _87515 x' s x f t => @lem3368746 _87504 _87515 x' s x f t h0) (fun h0 : term147 _87504 _87515 s x f x' t => @lem3368745 _87504 _87515 s x f x' t h0)). Qed.
Lemma lem3368748 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term166 _87504 _87515 s x f x' t) : (term166 _87504 _87515 s x f x' t) = False.
Proof. exact (prop_ext (fun h2 : term166 _87504 _87515 s x f x' t => @lem3368747 _87504 _87515 s x f x' t h1) (fun h2 : False => @lem3367994 _87504 _87515 s x f x' t h1)). Qed.
Lemma lem3368749 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (x' : _87504) (t : _87504 -> Prop) (h1 : term166 _87504 _87515 s x f x' t) : False.
Proof. exact (EQ_MP (@lem3368748 _87504 _87515 s x f x' t h1) (@lem3367994 _87504 _87515 s x f x' t h1)). Qed.
Lemma lem3368750 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term62 _87504 _87515 s x f t) : False.
Proof. exact (ex_elim (@lem3367848 _87504 _87515 s x f t h1) (fun x' : _87504 => fun h0 : term168 _87504 _87515 s x f t x' => @lem3368749 _87504 _87515 s x f x' t h0)). Qed.
Lemma lem3368751 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term62 _87504 _87515 s x f t) : (term62 _87504 _87515 s x f t) = False.
Proof. exact (prop_ext (fun h2 : term62 _87504 _87515 s x f t => @lem3368750 _87504 _87515 s x f t h1) (fun h2 : False => @lem3367347 _87504 _87515 s x f t h1)). Qed.
Lemma lem3368752 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) (h1 : term62 _87504 _87515 s x f t) : False.
Proof. exact (EQ_MP (@lem3368751 _87504 _87515 s x f t h1) (@lem3367347 _87504 _87515 s x f t h1)). Qed.
Lemma lem3368753 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : term61 _87504 _87515 s x f t.
Proof. exact (fun h0 : term62 _87504 _87515 s x f t => @lem3368752 _87504 _87515 s x f t h0). Qed.
Lemma lem3368754 {_87504 _87515 : Type'} (s : _87504 -> Prop) (x : _87515) (f : _87504 -> _87515) (t : _87504 -> Prop) : (term28 _87504 _87515 x f s t) = (term35 _87504 _87515 s x f t).
Proof. exact (EQ_MP (@lem3367346 _87504 _87515 s x f t) (@lem3368753 _87504 _87515 s x f t)). Qed.
Lemma lem3368759 {_87504 _87515 : Type'} (s : _87504 -> Prop) (f : _87504 -> _87515) (t : _87504 -> Prop) : term38 _87504 _87515 s f t.
Proof. exact (fun x : _87515 => @lem3368754 _87504 _87515 s x f t). Qed.
Lemma lem3368764 {_87504 _87515 : Type'} (s : _87504 -> Prop) (f : _87504 -> _87515) : term42 _87504 _87515 s f.
Proof. exact (fun t : _87504 -> Prop => @lem3368759 _87504 _87515 s f t). Qed.
Lemma lem3368769 {_87504 _87515 : Type'} (f : _87504 -> _87515) : term46 _87504 _87515 f.
Proof. exact (fun s : _87504 -> Prop => @lem3368764 _87504 _87515 s f). Qed.
Lemma lem3368774 {_87504 _87515 : Type'} : term50 _87504 _87515.
Proof. exact (fun f : _87504 -> _87515 => @lem3368769 _87504 _87515 f). Qed.
Lemma lem3368775 {_87504 _87515 : Type'} : term52 _87504 _87515.
Proof. exact (EQ_MP (@lem3367342 _87504 _87515) (@lem3368774 _87504 _87515)). Qed.
Lemma lem3368777 {_87504 _87515 : Type'} : term52 _87504 _87515.
Proof. exact (@lem3367059 _87504 _87515 (@lem3368775 _87504 _87515)). Qed.
Lemma lem3368778 {_87504 _87515 : Type'} (h1 : term53 _87504 _87515) : False.
Proof. exact (@lem3368777 _87504 _87515 (@lem3367043 _87504 _87515 h1)). Qed.
Lemma lem3368779 {_87504 _87515 : Type'} (h1 : term53 _87504 _87515) : (term53 _87504 _87515) = False.
Proof. exact (prop_ext (fun h2 : term53 _87504 _87515 => @lem3368778 _87504 _87515 h1) (fun h2 : False => @lem3367043 _87504 _87515 h1)). Qed.
Lemma lem3368780 {_87504 _87515 : Type'} (h1 : term53 _87504 _87515) : False.
Proof. exact (EQ_MP (@lem3368779 _87504 _87515 h1) (@lem3367043 _87504 _87515 h1)). Qed.
Lemma lem3368781 {_87504 _87515 : Type'} : term52 _87504 _87515.
Proof. exact (fun h0 : term53 _87504 _87515 => @lem3368780 _87504 _87515 h0). Qed.
Lemma lem3368782 {_87504 _87515 : Type'} : term50 _87504 _87515.
Proof. exact (EQ_MP (@lem3367042 _87504 _87515) (@lem3368781 _87504 _87515)). Qed.
Lemma lem3368783 {_87504 _87515 : Type'} : term49 _87504 _87515.
Proof. exact (EQ_MP (@lem3367038 _87504 _87515) (@lem3368782 _87504 _87515)). Qed.

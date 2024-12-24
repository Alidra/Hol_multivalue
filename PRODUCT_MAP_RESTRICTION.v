Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PRODUCT_MAP_RESTRICTION_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import RESTRICTION_spec.
Require Import product_map_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem4456753 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4456754 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem4456755 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem4456754 A B f) (@lem4456753 A B f)). Qed.
Lemma lem4456756 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem4456755 A B f g). Qed.
Lemma lem4456757 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem4456768 {A B : Type'} (s : A -> Prop) : term4 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4456769 {A B : Type'} (s : A -> Prop) : (term4 A B s) = (term5 A B s).
Proof. exact (eq_refl (term4 A B s)). Qed.
Lemma lem4456770 {A B : Type'} (s : A -> Prop) : term5 A B s.
Proof. exact (EQ_MP (@lem4456769 A B s) (@lem4456768 A B s)). Qed.
Lemma lem4456771 {A B : Type'} (s : A -> Prop) (f : A -> B) : term6 A B s f.
Proof. exact (@lem4456770 A B s f). Qed.
Lemma lem4456772 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term6 A B s f) = (term7 A B s f).
Proof. exact (eq_refl (term6 A B s f)). Qed.
Lemma lem4456773 {A B : Type'} (s : A -> Prop) (f : A -> B) : term7 A B s f.
Proof. exact (EQ_MP (@lem4456772 A B s f) (@lem4456771 A B s f)). Qed.
Lemma lem4456774 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term8 A B s f x.
Proof. exact (@lem4456773 A B s f x). Qed.
Lemma lem4456775 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term8 A B s f x) = ((@RESTRICTION A B s f x) = (term9 A B s f x)).
Proof. exact (eq_refl (term8 A B s f x)). Qed.
Lemma lem4456777 {A B K : Type'} (k : K -> Prop) : term10 A B K k.
Proof. exact (@lem4456752 A B K k). Qed.
Lemma lem4456778 {A B K : Type'} (k : K -> Prop) : (term10 A B K k) = (term11 A B K k).
Proof. exact (eq_refl (term10 A B K k)). Qed.
Lemma lem4456779 {A B K : Type'} (k : K -> Prop) : term11 A B K k.
Proof. exact (EQ_MP (@lem4456778 A B K k) (@lem4456777 A B K k)). Qed.
Lemma lem4456780 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : term12 A B K k f.
Proof. exact (@lem4456779 A B K k f). Qed.
Lemma lem4456781 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (term12 A B K k f) = ((@product_map A B K k f) = (term13 A B K k f)).
Proof. exact (eq_refl (term12 A B K k f)). Qed.
Lemma lem4456798 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem4456757 A B f g) (@lem4456756 A B f g)). Qed.
Lemma lem4456799 {B K : Type'} (f : K -> B) (g : K -> B) : (f = g) = (term14 B K f g).
Proof. exact (@lem4456798 K B f g). Qed.
Lemma lem4456800 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : ((term15 A B K f k x) = (term16 A B K k f x)) = (term17 A B K k f x).
Proof. exact (@lem4456799 B K (term15 A B K f k x) (term16 A B K k f x)). Qed.
Lemma lem4456810 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (@product_map A B K k f) = (term13 A B K k f).
Proof. exact (EQ_MP (@lem4456781 A B K k f) (@lem4456780 A B K k f)). Qed.
Lemma lem4456811 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (@product_map A B K k f) = (term13 A B K k f).
Proof. exact (@lem4456810 A B K k f). Qed.
Lemma lem4456812 {A K : Type'} (k : K -> Prop) (x : K -> A) : (@RESTRICTION K A k x) = (@RESTRICTION K A k x).
Proof. exact (eq_refl (@RESTRICTION K A k x)). Qed.
Lemma lem4456813 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term15 A B K f k x) = (term18 A B K f k x).
Proof. exact (MK_COMB (@lem4456811 A B K k f) (@lem4456812 A K k x)). Qed.
Lemma lem4456815 {A B : Type'} (f : A -> B) (y : A) : (term19 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4456816 {A B K : Type'} (f : type887 A B K) (y : K -> A) : (term20 A B K f y) = (f y).
Proof. exact (@lem4456815 (K -> A) (K -> B) f y). Qed.
Lemma lem4456817 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term21 A B K f k x) = (term18 A B K f k x).
Proof. exact (@lem4456816 A B K (term13 A B K k f) (@RESTRICTION K A k x)). Qed.
Lemma lem4456818 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term22 A B K k f x) = (term16 A B K k f x).
Proof. exact (eq_refl (term22 A B K k f x)). Qed.
Lemma lem4456819 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (term23 A B K k f) = (term13 A B K k f).
Proof. exact (fun_ext (fun x : K -> A => @lem4456818 A B K k f x)). Qed.
Lemma lem4456820 {A K : Type'} (k : K -> Prop) (x : K -> A) : (@RESTRICTION K A k x) = (@RESTRICTION K A k x).
Proof. exact (eq_refl (@RESTRICTION K A k x)). Qed.
Lemma lem4456821 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term21 A B K f k x) = (term18 A B K f k x).
Proof. exact (MK_COMB (@lem4456819 A B K k f) (@lem4456820 A K k x)). Qed.
Lemma lem4456822 {B K : Type'} : (@eq (K -> B)) = (@eq (K -> B)).
Proof. exact (eq_refl (@eq (K -> B))). Qed.
Lemma lem4456823 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term24 A B K f k x) = (term25 A B K f k x).
Proof. exact (MK_COMB (@lem4456822 B K) (@lem4456821 A B K f k x)). Qed.
Lemma lem4456824 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term18 A B K f k x) = (term26 A B K f k x).
Proof. exact (eq_refl (term18 A B K f k x)). Qed.
Lemma lem4456825 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : ((term21 A B K f k x) = (term18 A B K f k x)) = ((term18 A B K f k x) = (term26 A B K f k x)).
Proof. exact (MK_COMB (@lem4456823 A B K f k x) (@lem4456824 A B K f k x)). Qed.
Lemma lem4456826 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term18 A B K f k x) = (term26 A B K f k x).
Proof. exact (EQ_MP (@lem4456825 A B K f k x) (@lem4456817 A B K f k x)). Qed.
Lemma lem4456828 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term9 A B s f x).
Proof. exact (EQ_MP (@lem4456775 A B s f x) (@lem4456774 A B s f x)). Qed.
Lemma lem4456829 {A K : Type'} (s : K -> Prop) (f : K -> A) (x : K) : (@RESTRICTION K A s f x) = (term27 A K s f x).
Proof. exact (@lem4456828 K A s f x). Qed.
Lemma lem4456830 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (@RESTRICTION K A k x i) = (term27 A K k x i).
Proof. exact (@lem4456829 A K k x i). Qed.
Lemma lem4456864 {A B K : Type'} (f : type1514 A B K) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4456865 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term28 A B K f k x i) = (term29 A B K f k x i).
Proof. exact (MK_COMB (@lem4456864 A B K f i) (@lem4456830 A K k x i)). Qed.
Lemma lem4456899 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term30 A B K f k x) = (term31 A B K f k x).
Proof. exact (fun_ext (fun i : K => @lem4456865 A B K f k x i)). Qed.
Lemma lem4456933 {B K : Type'} (k : K -> Prop) : (@RESTRICTION K B k) = (@RESTRICTION K B k).
Proof. exact (eq_refl (@RESTRICTION K B k)). Qed.
Lemma lem4456934 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term26 A B K f k x) = (term32 A B K f k x).
Proof. exact (MK_COMB (@lem4456933 B K k) (@lem4456899 A B K f k x)). Qed.
Lemma lem4456968 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term18 A B K f k x) = (term32 A B K f k x).
Proof. exact (TRANS (@lem4456826 A B K f k x) (@lem4456934 A B K f k x)). Qed.
Lemma lem4456969 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term15 A B K f k x) = (term32 A B K f k x).
Proof. exact (TRANS (@lem4456813 A B K f k x) (@lem4456968 A B K f k x)). Qed.
Lemma lem4456970 {K : Type'} (x : K) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4456971 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term33 A B K f k x x') = (term34 A B K f k x x').
Proof. exact (MK_COMB (@lem4456969 A B K f k x) (@lem4456970 K x')). Qed.
Lemma lem4456973 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term9 A B s f x).
Proof. exact (EQ_MP (@lem4456775 A B s f x) (@lem4456774 A B s f x)). Qed.
Lemma lem4456974 {B K : Type'} (s : K -> Prop) (f : K -> B) (x : K) : (@RESTRICTION K B s f x) = (term27 B K s f x).
Proof. exact (@lem4456973 K B s f x). Qed.
Lemma lem4456975 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term34 A B K f k x x') = (term35 A B K f k x x').
Proof. exact (@lem4456974 B K k (term31 A B K f k x) x'). Qed.
Lemma lem4456977 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term36 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4456978 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term37 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4456977 _2963 g t e g' t' e'). Qed.
Lemma lem4456979 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term38 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4456978 _2963 g t e g' t'). Qed.
Lemma lem4456980 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term39 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4456979 _2963 g t e g'). Qed.
Lemma lem4456981 {B : Type'} (g : Prop) (t : B) (e : B) : term39 B g t e.
Proof. exact (@lem4456980 B g t e). Qed.
Lemma lem4456982 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : term40 A B K f k x x'.
Proof. exact (@lem4456981 B (@IN K x' k) (term41 A B K f k x x') (@ARB B)). Qed.
Lemma lem4456983 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) : term42 A B K f k x x' g'.
Proof. exact (@lem4456982 A B K f k x x' g'). Qed.
Lemma lem4456984 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) : (term42 A B K f k x x' g') = (term43 A B K f k x x' g').
Proof. exact (eq_refl (term42 A B K f k x x' g')). Qed.
Lemma lem4456985 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) : term43 A B K f k x x' g'.
Proof. exact (EQ_MP (@lem4456984 A B K f k x x' g') (@lem4456983 A B K f k x x' g')). Qed.
Lemma lem4456986 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) (t' : B) : term44 A B K f k x x' g' t'.
Proof. exact (@lem4456985 A B K f k x x' g' t'). Qed.
Lemma lem4456987 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) (t' : B) : (term44 A B K f k x x' g' t') = (term45 A B K f k x x' g' t').
Proof. exact (eq_refl (term44 A B K f k x x' g' t')). Qed.
Lemma lem4456988 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) (t' : B) : term45 A B K f k x x' g' t'.
Proof. exact (EQ_MP (@lem4456987 A B K f k x x' g' t') (@lem4456986 A B K f k x x' g' t')). Qed.
Lemma lem4456989 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) (t' : B) (e' : B) : term46 A B K f k x x' g' t' e'.
Proof. exact (@lem4456988 A B K f k x x' g' t' e'). Qed.
Lemma lem4456990 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) (t' : B) (e' : B) : (term46 A B K f k x x' g' t' e') = (term47 A B K f k x x' g' t' e').
Proof. exact (eq_refl (term46 A B K f k x x' g' t' e')). Qed.
Lemma lem4456991 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) (t' : B) (e' : B) : term47 A B K f k x x' g' t' e'.
Proof. exact (EQ_MP (@lem4456990 A B K f k x x' g' t' e') (@lem4456989 A B K f k x x' g' t' e')). Qed.
Lemma lem4456992 {K : Type'} (x : K) (k : K -> Prop) : (@IN K x k) = (@IN K x k).
Proof. exact (eq_refl (@IN K x k)). Qed.
Lemma lem4456993 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K) (k : K -> Prop) (t' : B) (e' : B) : term48 A B K f x x' k t' e'.
Proof. exact (@lem4456991 A B K f k x x' (@IN K x' k) t' e'). Qed.
Lemma lem4456994 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K) (k : K -> Prop) (t' : B) (e' : B) : term49 A B K f x x' k t' e'.
Proof. exact (@lem4456993 A B K f x x' k t' e' (@lem4456992 K x' k)). Qed.
Lemma lem4456995 {K : Type'} (x : K) (k : K -> Prop) (h1 : @IN K x k) : @IN K x k.
Proof. exact (h1). Qed.
Lemma lem4456996 {K : Type'} (x : K) (k : K -> Prop) : (@IN K x k) = ((@IN K x k) = True).
Proof. exact (@lem7 (@IN K x k)). Qed.
Lemma lem4456999 {A B : Type'} (f : A -> B) (y : A) : (term19 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4457000 {B K : Type'} (f : K -> B) (y : K) : (term50 B K f y) = (f y).
Proof. exact (@lem4456999 K B f y). Qed.
Lemma lem4457001 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term51 A B K f k x x') = (term41 A B K f k x x').
Proof. exact (@lem4457000 B K (term31 A B K f k x) x'). Qed.
Lemma lem4457002 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term41 A B K f k x i) = (term29 A B K f k x i).
Proof. exact (eq_refl (term41 A B K f k x i)). Qed.
Lemma lem4457003 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term52 A B K f k x) = (term31 A B K f k x).
Proof. exact (fun_ext (fun i : K => @lem4457002 A B K f k x i)). Qed.
Lemma lem4457004 {K : Type'} (x : K) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4457005 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term51 A B K f k x x') = (term41 A B K f k x x').
Proof. exact (MK_COMB (@lem4457003 A B K f k x) (@lem4457004 K x')). Qed.
Lemma lem4457006 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4457007 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term53 A B K f k x x') = (term54 A B K f k x x').
Proof. exact (MK_COMB (@lem4457006 B) (@lem4457005 A B K f k x x')). Qed.
Lemma lem4457008 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term41 A B K f k x x') = (term29 A B K f k x x').
Proof. exact (eq_refl (term41 A B K f k x x')). Qed.
Lemma lem4457009 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : ((term51 A B K f k x x') = (term41 A B K f k x x')) = ((term41 A B K f k x x') = (term29 A B K f k x x')).
Proof. exact (MK_COMB (@lem4457007 A B K f k x x') (@lem4457008 A B K f k x x')). Qed.
Lemma lem4457010 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term41 A B K f k x x') = (term29 A B K f k x x').
Proof. exact (EQ_MP (@lem4457009 A B K f k x x') (@lem4457001 A B K f k x x')). Qed.
Lemma lem4457012 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term36 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4457013 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term37 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4457012 _2963 g t e g' t' e'). Qed.
Lemma lem4457014 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term38 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4457013 _2963 g t e g' t'). Qed.
Lemma lem4457015 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term39 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4457014 _2963 g t e g'). Qed.
Lemma lem4457016 {A : Type'} (g : Prop) (t : A) (e : A) : term39 A g t e.
Proof. exact (@lem4457015 A g t e). Qed.
Lemma lem4457017 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : term55 A K k x x'.
Proof. exact (@lem4457016 A (@IN K x' k) (x x') (@ARB A)). Qed.
Lemma lem4457018 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) : term56 A K k x x' g'.
Proof. exact (@lem4457017 A K k x x' g'). Qed.
Lemma lem4457019 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) : (term56 A K k x x' g') = (term57 A K k x x' g').
Proof. exact (eq_refl (term56 A K k x x' g')). Qed.
Lemma lem4457020 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) : term57 A K k x x' g'.
Proof. exact (EQ_MP (@lem4457019 A K k x x' g') (@lem4457018 A K k x x' g')). Qed.
Lemma lem4457021 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) (t' : A) : term58 A K k x x' g' t'.
Proof. exact (@lem4457020 A K k x x' g' t'). Qed.
Lemma lem4457022 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) (t' : A) : (term58 A K k x x' g' t') = (term59 A K k x x' g' t').
Proof. exact (eq_refl (term58 A K k x x' g' t')). Qed.
Lemma lem4457023 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) (t' : A) : term59 A K k x x' g' t'.
Proof. exact (EQ_MP (@lem4457022 A K k x x' g' t') (@lem4457021 A K k x x' g' t')). Qed.
Lemma lem4457024 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) (t' : A) (e' : A) : term60 A K k x x' g' t' e'.
Proof. exact (@lem4457023 A K k x x' g' t' e'). Qed.
Lemma lem4457025 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) (t' : A) (e' : A) : (term60 A K k x x' g' t' e') = (term61 A K k x x' g' t' e').
Proof. exact (eq_refl (term60 A K k x x' g' t' e')). Qed.
Lemma lem4457026 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (g' : Prop) (t' : A) (e' : A) : term61 A K k x x' g' t' e'.
Proof. exact (EQ_MP (@lem4457025 A K k x x' g' t' e') (@lem4457024 A K k x x' g' t' e')). Qed.
Lemma lem4457028 {K : Type'} (x : K) (k : K -> Prop) (h1 : @IN K x k) : (@IN K x k) = True.
Proof. exact (EQ_MP (@lem4456996 K x k) (@lem4456995 K x k h1)). Qed.
Lemma lem4457029 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) (t' : A) (e' : A) : term62 A K k x x' t' e'.
Proof. exact (@lem4457026 A K k x x' True t' e'). Qed.
Lemma lem4457030 {A K : Type'} (x : K -> A) (t' : A) (e' : A) (x' : K) (k : K -> Prop) (h1 : @IN K x' k) : term63 A K k x x' t' e'.
Proof. exact (@lem4457029 A K k x x' t' e' (@lem4457028 K x' k h1)). Qed.
Lemma lem4457036 {A K : Type'} (x : K -> A) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4457037 {A K : Type'} (x : K -> A) (x' : K) : term64 A K x x'.
Proof. exact (fun h0 : True => @lem4457036 A K x x'). Qed.
Lemma lem4457038 {A K : Type'} (x : K -> A) (e' : A) (x' : K) (k : K -> Prop) (h1 : @IN K x' k) : term65 A K k x x' e'.
Proof. exact (@lem4457030 A K x (x x') e' x' k h1). Qed.
Lemma lem4457039 {A K : Type'} (x : K -> A) (e' : A) (x' : K) (k : K -> Prop) (h1 : @IN K x' k) : term66 A K k x x' e'.
Proof. exact (@lem4457038 A K x e' x' k h1 (@lem4457037 A K x x')). Qed.
Lemma lem4457043 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4457044 {A : Type'} : term67 A.
Proof. exact (fun h0 : ~ True => @lem4457043 A). Qed.
Lemma lem4457045 {A K : Type'} (x : K -> A) (x' : K) (k : K -> Prop) (h1 : @IN K x' k) : term68 A K k x x'.
Proof. exact (@lem4457039 A K x (@ARB A) x' k h1). Qed.
Lemma lem4457046 {A K : Type'} (x : K -> A) (x' : K) (k : K -> Prop) (h1 : @IN K x' k) : (term27 A K k x x') = (term69 A K x x').
Proof. exact (@lem4457045 A K x x' k h1 (@lem4457044 A)). Qed.
Lemma lem4457048 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4457049 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4457048 A t2 t1). Qed.
Lemma lem4457050 {A K : Type'} (x : K -> A) (x' : K) : (term69 A K x x') = (x x').
Proof. exact (@lem4457049 A (@ARB A) (x x')). Qed.
Lemma lem4457051 {A K : Type'} (x : K -> A) (x' : K) (k : K -> Prop) (h1 : @IN K x' k) : (term27 A K k x x') = (x x').
Proof. exact (TRANS (@lem4457046 A K x x' k h1) (@lem4457050 A K x x')). Qed.
Lemma lem4457052 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4457053 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K) (k : K -> Prop) (h1 : @IN K x' k) : (term29 A B K f k x x') = (term70 A B K f x x').
Proof. exact (MK_COMB (@lem4457052 A B K f x') (@lem4457051 A K x x' k h1)). Qed.
Lemma lem4457054 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K) (k : K -> Prop) (h1 : @IN K x' k) : (term41 A B K f k x x') = (term70 A B K f x x').
Proof. exact (TRANS (@lem4457010 A B K f k x x') (@lem4457053 A B K f x x' k h1)). Qed.
Lemma lem4457055 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : term71 A B K k f x x'.
Proof. exact (fun h0 : @IN K x' k => @lem4457054 A B K f x x' k h0). Qed.
Lemma lem4457056 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (e' : B) : term72 A B K k f x x' e'.
Proof. exact (@lem4456994 A B K f x x' k (term70 A B K f x x') e'). Qed.
Lemma lem4457057 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (e' : B) : term73 A B K k f x x' e'.
Proof. exact (@lem4457056 A B K k f x x' e' (@lem4457055 A B K k f x x')). Qed.
Lemma lem4457061 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4457062 {B K : Type'} (x : K) (k : K -> Prop) : term74 B K x k.
Proof. exact (fun h0 : term75 K x k => @lem4457061 B). Qed.
Lemma lem4457063 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : term76 A B K k f x x'.
Proof. exact (@lem4457057 A B K k f x x' (@ARB B)). Qed.
Lemma lem4457064 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : (term35 A B K f k x x') = (term77 A B K k f x x').
Proof. exact (@lem4457063 A B K k f x x' (@lem4457062 B K x' k)). Qed.
Lemma lem4457098 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : (term34 A B K f k x x') = (term77 A B K k f x x').
Proof. exact (TRANS (@lem4456975 A B K f k x x') (@lem4457064 A B K k f x x')). Qed.
Lemma lem4457099 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : (term33 A B K f k x x') = (term77 A B K k f x x').
Proof. exact (TRANS (@lem4456971 A B K f k x x') (@lem4457098 A B K k f x x')). Qed.
Lemma lem4457100 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4457101 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : (term78 A B K f k x x') = (term79 A B K k f x x').
Proof. exact (MK_COMB (@lem4457100 B) (@lem4457099 A B K k f x x')). Qed.
Lemma lem4457136 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term9 A B s f x).
Proof. exact (EQ_MP (@lem4456775 A B s f x) (@lem4456774 A B s f x)). Qed.
Lemma lem4457137 {B K : Type'} (s : K -> Prop) (f : K -> B) (x : K) : (@RESTRICTION K B s f x) = (term27 B K s f x).
Proof. exact (@lem4457136 K B s f x). Qed.
Lemma lem4457138 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : (term80 A B K k f x x') = (term81 A B K k f x x').
Proof. exact (@lem4457137 B K k (term82 A B K f x) x'). Qed.
Lemma lem4457140 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term36 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4457141 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term37 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4457140 _2963 g t e g' t' e'). Qed.
Lemma lem4457142 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term38 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4457141 _2963 g t e g' t'). Qed.
Lemma lem4457143 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term39 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4457142 _2963 g t e g'). Qed.
Lemma lem4457144 {B : Type'} (g : Prop) (t : B) (e : B) : term39 B g t e.
Proof. exact (@lem4457143 B g t e). Qed.
Lemma lem4457145 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : term83 A B K k f x x'.
Proof. exact (@lem4457144 B (@IN K x' k) (term84 A B K f x x') (@ARB B)). Qed.
Lemma lem4457146 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (g' : Prop) : term85 A B K k f x x' g'.
Proof. exact (@lem4457145 A B K k f x x' g'). Qed.
Lemma lem4457147 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (g' : Prop) : (term85 A B K k f x x' g') = (term86 A B K k f x x' g').
Proof. exact (eq_refl (term85 A B K k f x x' g')). Qed.
Lemma lem4457148 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (g' : Prop) : term86 A B K k f x x' g'.
Proof. exact (EQ_MP (@lem4457147 A B K k f x x' g') (@lem4457146 A B K k f x x' g')). Qed.
Lemma lem4457149 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (g' : Prop) (t' : B) : term87 A B K k f x x' g' t'.
Proof. exact (@lem4457148 A B K k f x x' g' t'). Qed.
Lemma lem4457150 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (g' : Prop) (t' : B) : (term87 A B K k f x x' g' t') = (term88 A B K k f x x' g' t').
Proof. exact (eq_refl (term87 A B K k f x x' g' t')). Qed.
Lemma lem4457151 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (g' : Prop) (t' : B) : term88 A B K k f x x' g' t'.
Proof. exact (EQ_MP (@lem4457150 A B K k f x x' g' t') (@lem4457149 A B K k f x x' g' t')). Qed.
Lemma lem4457152 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (g' : Prop) (t' : B) (e' : B) : term89 A B K k f x x' g' t' e'.
Proof. exact (@lem4457151 A B K k f x x' g' t' e'). Qed.
Lemma lem4457153 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (g' : Prop) (t' : B) (e' : B) : (term89 A B K k f x x' g' t' e') = (term90 A B K k f x x' g' t' e').
Proof. exact (eq_refl (term89 A B K k f x x' g' t' e')). Qed.
Lemma lem4457154 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (g' : Prop) (t' : B) (e' : B) : term90 A B K k f x x' g' t' e'.
Proof. exact (EQ_MP (@lem4457153 A B K k f x x' g' t' e') (@lem4457152 A B K k f x x' g' t' e')). Qed.
Lemma lem4457155 {K : Type'} (x : K) (k : K -> Prop) : (@IN K x k) = (@IN K x k).
Proof. exact (eq_refl (@IN K x k)). Qed.
Lemma lem4457156 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K) (k : K -> Prop) (t' : B) (e' : B) : term91 A B K f x x' k t' e'.
Proof. exact (@lem4457154 A B K k f x x' (@IN K x' k) t' e'). Qed.
Lemma lem4457157 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K) (k : K -> Prop) (t' : B) (e' : B) : term92 A B K f x x' k t' e'.
Proof. exact (@lem4457156 A B K f x x' k t' e' (@lem4457155 K x' k)). Qed.
Lemma lem4457162 {A B : Type'} (f : A -> B) (y : A) : (term19 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4457163 {B K : Type'} (f : K -> B) (y : K) : (term50 B K f y) = (f y).
Proof. exact (@lem4457162 K B f y). Qed.
Lemma lem4457164 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K) : (term93 A B K f x x') = (term84 A B K f x x').
Proof. exact (@lem4457163 B K (term82 A B K f x) x'). Qed.
Lemma lem4457165 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : K) : (term84 A B K f x i) = (term70 A B K f x i).
Proof. exact (eq_refl (term84 A B K f x i)). Qed.
Lemma lem4457166 {A B K : Type'} (f : type1514 A B K) (x : K -> A) : (term94 A B K f x) = (term82 A B K f x).
Proof. exact (fun_ext (fun i : K => @lem4457165 A B K f x i)). Qed.
Lemma lem4457167 {K : Type'} (x : K) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4457168 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K) : (term93 A B K f x x') = (term84 A B K f x x').
Proof. exact (MK_COMB (@lem4457166 A B K f x) (@lem4457167 K x')). Qed.
Lemma lem4457169 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4457170 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K) : (term95 A B K f x x') = (term96 A B K f x x').
Proof. exact (MK_COMB (@lem4457169 B) (@lem4457168 A B K f x x')). Qed.
Lemma lem4457171 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K) : (term84 A B K f x x') = (term70 A B K f x x').
Proof. exact (eq_refl (term84 A B K f x x')). Qed.
Lemma lem4457172 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K) : ((term93 A B K f x x') = (term84 A B K f x x')) = ((term84 A B K f x x') = (term70 A B K f x x')).
Proof. exact (MK_COMB (@lem4457170 A B K f x x') (@lem4457171 A B K f x x')). Qed.
Lemma lem4457173 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K) : (term84 A B K f x x') = (term70 A B K f x x').
Proof. exact (EQ_MP (@lem4457172 A B K f x x') (@lem4457164 A B K f x x')). Qed.
Lemma lem4457174 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : term97 A B K k f x x'.
Proof. exact (fun h0 : @IN K x' k => @lem4457173 A B K f x x'). Qed.
Lemma lem4457175 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (e' : B) : term98 A B K k f x x' e'.
Proof. exact (@lem4457157 A B K f x x' k (term70 A B K f x x') e'). Qed.
Lemma lem4457176 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) (e' : B) : term99 A B K k f x x' e'.
Proof. exact (@lem4457175 A B K k f x x' e' (@lem4457174 A B K k f x x')). Qed.
Lemma lem4457180 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4457181 {B K : Type'} (x : K) (k : K -> Prop) : term74 B K x k.
Proof. exact (fun h0 : term75 K x k => @lem4457180 B). Qed.
Lemma lem4457182 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : term100 A B K k f x x'.
Proof. exact (@lem4457176 A B K k f x x' (@ARB B)). Qed.
Lemma lem4457183 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : (term81 A B K k f x x') = (term77 A B K k f x x').
Proof. exact (@lem4457182 A B K k f x x' (@lem4457181 B K x' k)). Qed.
Lemma lem4457217 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : (term80 A B K k f x x') = (term77 A B K k f x x').
Proof. exact (TRANS (@lem4457138 A B K k f x x') (@lem4457183 A B K k f x x')). Qed.
Lemma lem4457218 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : ((term33 A B K f k x x') = (term80 A B K k f x x')) = ((term77 A B K k f x x') = (term77 A B K k f x x')).
Proof. exact (MK_COMB (@lem4457101 A B K k f x x') (@lem4457217 A B K k f x x')). Qed.
Lemma lem4457220 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4457221 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4457220 B x). Qed.
Lemma lem4457222 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : ((term77 A B K k f x x') = (term77 A B K k f x x')) = True.
Proof. exact (@lem4457221 B (term77 A B K k f x x')). Qed.
Lemma lem4457223 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K) : ((term33 A B K f k x x') = (term80 A B K k f x x')) = True.
Proof. exact (TRANS (@lem4457218 A B K k f x x') (@lem4457222 A B K k f x x')). Qed.
Lemma lem4457224 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term101 A B K k f x) = (term102 K).
Proof. exact (fun_ext (fun x' : K => @lem4457223 A B K k f x x')). Qed.
Lemma lem4457225 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4457226 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term17 A B K k f x) = (term103 K).
Proof. exact (MK_COMB (@lem4457225 K) (@lem4457224 A B K k f x)). Qed.
Lemma lem4457228 {A : Type'} (t : Prop) : (term104 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4457229 {K : Type'} (t : Prop) : (term104 K t) = t.
Proof. exact (@lem4457228 K t). Qed.
Lemma lem4457230 {K : Type'} : (term103 K) = True.
Proof. exact (@lem4457229 K True). Qed.
Lemma lem4457231 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term17 A B K k f x) = True.
Proof. exact (TRANS (@lem4457226 A B K k f x) (@lem4457230 K)). Qed.
Lemma lem4457232 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : ((term15 A B K f k x) = (term16 A B K k f x)) = True.
Proof. exact (TRANS (@lem4456800 A B K k f x) (@lem4457231 A B K k f x)). Qed.
Lemma lem4457233 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (term105 A B K k f) = (term106 A K).
Proof. exact (fun_ext (fun x : K -> A => @lem4457232 A B K k f x)). Qed.
Lemma lem4457234 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4457235 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (term107 A B K k f) = (term108 A K).
Proof. exact (MK_COMB (@lem4457234 A K) (@lem4457233 A B K k f)). Qed.
Lemma lem4457237 {A : Type'} (t : Prop) : (term104 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4457238 {A K : Type'} (t : Prop) : (term109 A K t) = t.
Proof. exact (@lem4457237 (K -> A) t). Qed.
Lemma lem4457239 {A K : Type'} : (term108 A K) = True.
Proof. exact (@lem4457238 A K True). Qed.
Lemma lem4457240 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (term107 A B K k f) = True.
Proof. exact (TRANS (@lem4457235 A B K k f) (@lem4457239 A K)). Qed.
Lemma lem4457241 {A B K : Type'} (f : type1514 A B K) : (term110 A B K f) = (term111 K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4457240 A B K k f)). Qed.
Lemma lem4457242 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4457243 {A B K : Type'} (f : type1514 A B K) : (term112 A B K f) = (term113 K).
Proof. exact (MK_COMB (@lem4457242 K) (@lem4457241 A B K f)). Qed.
Lemma lem4457245 {A : Type'} (t : Prop) : (term104 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4457246 {K : Type'} (t : Prop) : (term114 K t) = t.
Proof. exact (@lem4457245 (K -> Prop) t). Qed.
Lemma lem4457247 {K : Type'} : (term113 K) = True.
Proof. exact (@lem4457246 K True). Qed.
Lemma lem4457248 {A B K : Type'} (f : type1514 A B K) : (term112 A B K f) = True.
Proof. exact (TRANS (@lem4457243 A B K f) (@lem4457247 K)). Qed.
Lemma lem4457249 {A B K : Type'} : (term115 A B K) = (term116 A B K).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4457248 A B K f)). Qed.
Lemma lem4457250 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4457251 {A B K : Type'} : (term117 A B K) = (term118 A B K).
Proof. exact (MK_COMB (@lem4457250 A B K) (@lem4457249 A B K)). Qed.
Lemma lem4457253 {A : Type'} (t : Prop) : (term104 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4457254 {A B K : Type'} (t : Prop) : (term119 A B K t) = t.
Proof. exact (@lem4457253 (type1514 A B K) t). Qed.
Lemma lem4457255 {A B K : Type'} : (term118 A B K) = True.
Proof. exact (@lem4457254 A B K True). Qed.
Lemma lem4457256 {A B K : Type'} : (term117 A B K) = True.
Proof. exact (TRANS (@lem4457251 A B K) (@lem4457255 A B K)). Qed.
Lemma lem4457257 {A B K : Type'} : True = (term117 A B K).
Proof. exact (SYM (@lem4457256 A B K)). Qed.
Lemma lem4457258 {A B K : Type'} : term117 A B K.
Proof. exact (EQ_MP (@lem4457257 A B K) (@lem0)). Qed.

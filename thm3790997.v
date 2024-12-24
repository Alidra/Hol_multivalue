Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3790997_term_abbrevs.
Require Import thm3789889_spec.
Require Import thm3790897_spec.
Lemma lem3790898 {A B : Type'} : (term0 A B) = (term1 A B).
Proof. exact (eq_refl (term0 A B)). Qed.
Lemma lem3790899 {A B : Type'} : term1 A B.
Proof. exact (EQ_MP (@lem3790898 A B) (@lem3789889 A B)). Qed.
Lemma lem3790900 {A B : Type'} : term2 A B.
Proof. exact (@lem3790899 A B term3). Qed.
Lemma lem3790901 {A B : Type'} : (term2 A B) = (term4 A B).
Proof. exact (eq_refl (term2 A B)). Qed.
Lemma lem3790902 {A B : Type'} : term4 A B.
Proof. exact (EQ_MP (@lem3790901 A B) (@lem3790900 A B)). Qed.
Lemma lem3790903 {A B : Type'} (h1 : (@FINREC A B) = (term5 A B)) : (@FINREC A B) = (term5 A B).
Proof. exact (h1). Qed.
Lemma lem3790904 {A B : Type'} (h1 : (@FINREC A B) = (term5 A B)) : (term5 A B) = (@FINREC A B).
Proof. exact (SYM (@lem3790903 A B h1)). Qed.
Lemma lem3790905 {A B : Type'} (h1 : (term5 A B) = (@FINREC A B)) : (term5 A B) = (@FINREC A B).
Proof. exact (h1). Qed.
Lemma lem3790906 {A B : Type'} (h1 : (term5 A B) = (@FINREC A B)) : (@FINREC A B) = (term5 A B).
Proof. exact (SYM (@lem3790905 A B h1)). Qed.
Lemma lem3790907 {A B : Type'} : ((@FINREC A B) = (term5 A B)) = ((term5 A B) = (@FINREC A B)).
Proof. exact (prop_ext (fun h1 : (@FINREC A B) = (term5 A B) => @lem3790904 A B h1) (fun h1 : (term5 A B) = (@FINREC A B) => @lem3790906 A B h1)). Qed.
Lemma lem3790910 {A B : Type'} : (term5 A B) = (@FINREC A B).
Proof. exact (EQ_MP (@lem3790907 A B) (@lem3790897 A B)). Qed.
Lemma lem3790911 {A B : Type'} : (term5 A B) = (@FINREC A B).
Proof. exact (@lem3790910 A B). Qed.
Lemma lem3790912 {A B : Type'} (f : type1411 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3790913 {A B : Type'} (f : type1411 A B) : (term6 A B f) = (@FINREC A B f).
Proof. exact (MK_COMB (@lem3790911 A B) (@lem3790912 A B f)). Qed.
Lemma lem3790914 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3790915 {A B : Type'} (f : type1411 A B) (b : B) : (term7 A B f b) = (@FINREC A B f b).
Proof. exact (MK_COMB (@lem3790913 A B f) (@lem3790914 B b)). Qed.
Lemma lem3790916 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3790917 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term8 A B f b s) = (@FINREC A B f b s).
Proof. exact (MK_COMB (@lem3790915 A B f b) (@lem3790916 A s)). Qed.
Lemma lem3790918 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3790919 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term9 A B f b s a) = (@FINREC A B f b s a).
Proof. exact (MK_COMB (@lem3790917 A B f b s) (@lem3790918 B a)). Qed.
Lemma lem3790920 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem3790921 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term10 A B f b s a) = (term11 A B f b s a).
Proof. exact (MK_COMB (@lem3790919 A B f b s a) (@lem3790920)). Qed.
Lemma lem3790922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3790923 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term12 A B f b s a) = (term13 A B f b s a).
Proof. exact (MK_COMB (@lem3790922) (@lem3790921 A B f b s a)). Qed.
Lemma lem3790924 {A B : Type'} (s : A -> Prop) (a : B) (b : B) : (term14 A B s a b) = (term14 A B s a b).
Proof. exact (eq_refl (term14 A B s a b)). Qed.
Lemma lem3790925 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : ((term10 A B f b s a) = (term14 A B s a b)) = ((term11 A B f b s a) = (term14 A B s a b)).
Proof. exact (MK_COMB (@lem3790923 A B f b s a) (@lem3790924 A B s a b)). Qed.
Lemma lem3790926 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) : (term15 A B f s a) = (term16 A B f s a).
Proof. exact (fun_ext (fun b : B => @lem3790925 A B f s a b)). Qed.
Lemma lem3790927 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3790928 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) : (term17 A B f s a) = (term18 A B f s a).
Proof. exact (MK_COMB (@lem3790927 B) (@lem3790926 A B f s a)). Qed.
Lemma lem3790929 {A B : Type'} (f : type1411 A B) (s : A -> Prop) : (term19 A B f s) = (term20 A B f s).
Proof. exact (fun_ext (fun a : B => @lem3790928 A B f s a)). Qed.
Lemma lem3790930 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3790931 {A B : Type'} (f : type1411 A B) (s : A -> Prop) : (term21 A B f s) = (term22 A B f s).
Proof. exact (MK_COMB (@lem3790930 B) (@lem3790929 A B f s)). Qed.
Lemma lem3790932 {A B : Type'} (f : type1411 A B) : (term23 A B f) = (term24 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3790931 A B f s)). Qed.
Lemma lem3790933 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3790934 {A B : Type'} (f : type1411 A B) : (term25 A B f) = (term26 A B f).
Proof. exact (MK_COMB (@lem3790933 A) (@lem3790932 A B f)). Qed.
Lemma lem3790935 {A B : Type'} : (term27 A B) = (term28 A B).
Proof. exact (fun_ext (fun f : type1411 A B => @lem3790934 A B f)). Qed.
Lemma lem3790936 {A B : Type'} : (@all (A -> B -> B)) = (@all (A -> B -> B)).
Proof. exact (eq_refl (@all (A -> B -> B))). Qed.
Lemma lem3790937 {A B : Type'} : (term29 A B) = (term30 A B).
Proof. exact (MK_COMB (@lem3790936 A B) (@lem3790935 A B)). Qed.
Lemma lem3790938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3790939 {A B : Type'} : (term31 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem3790938) (@lem3790937 A B)). Qed.
Lemma lem3790941 {A B : Type'} : (term5 A B) = (@FINREC A B).
Proof. exact (EQ_MP (@lem3790907 A B) (@lem3790897 A B)). Qed.
Lemma lem3790942 {A B : Type'} : (term5 A B) = (@FINREC A B).
Proof. exact (@lem3790941 A B). Qed.
Lemma lem3790943 {A B : Type'} (f : type1411 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3790944 {A B : Type'} (f : type1411 A B) : (term6 A B f) = (@FINREC A B f).
Proof. exact (MK_COMB (@lem3790942 A B) (@lem3790943 A B f)). Qed.
Lemma lem3790945 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3790946 {A B : Type'} (f : type1411 A B) (b : B) : (term7 A B f b) = (@FINREC A B f b).
Proof. exact (MK_COMB (@lem3790944 A B f) (@lem3790945 B b)). Qed.
Lemma lem3790947 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3790948 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) : (term8 A B f b s) = (@FINREC A B f b s).
Proof. exact (MK_COMB (@lem3790946 A B f b) (@lem3790947 A s)). Qed.
Lemma lem3790949 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3790950 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) : (term9 A B f b s a) = (@FINREC A B f b s a).
Proof. exact (MK_COMB (@lem3790948 A B f b s) (@lem3790949 B a)). Qed.
Lemma lem3790951 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem3790952 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) : (term33 A B f b s a n) = (term34 A B f b s a n).
Proof. exact (MK_COMB (@lem3790950 A B f b s a) (@lem3790951 n)). Qed.
Lemma lem3790953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3790954 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a : B) (n : nat) : (term35 A B f b s a n) = (term36 A B f b s a n).
Proof. exact (MK_COMB (@lem3790953) (@lem3790952 A B f b s a n)). Qed.
Lemma lem3790956 {A B : Type'} : (term5 A B) = (@FINREC A B).
Proof. exact (EQ_MP (@lem3790907 A B) (@lem3790897 A B)). Qed.
Lemma lem3790957 {A B : Type'} : (term5 A B) = (@FINREC A B).
Proof. exact (@lem3790956 A B). Qed.
Lemma lem3790958 {A B : Type'} (f : type1411 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3790959 {A B : Type'} (f : type1411 A B) : (term6 A B f) = (@FINREC A B f).
Proof. exact (MK_COMB (@lem3790957 A B) (@lem3790958 A B f)). Qed.
Lemma lem3790960 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3790961 {A B : Type'} (f : type1411 A B) (b : B) : (term7 A B f b) = (@FINREC A B f b).
Proof. exact (MK_COMB (@lem3790959 A B f) (@lem3790960 B b)). Qed.
Lemma lem3790962 {A : Type'} (s : A -> Prop) (x : A) : (@DELETE A s x) = (@DELETE A s x).
Proof. exact (eq_refl (@DELETE A s x)). Qed.
Lemma lem3790963 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) : (term37 A B f b s x) = (term38 A B f b s x).
Proof. exact (MK_COMB (@lem3790961 A B f b) (@lem3790962 A s x)). Qed.
Lemma lem3790964 {B : Type'} (c : B) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem3790965 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) : (term39 A B f b s x c) = (term40 A B f b s x c).
Proof. exact (MK_COMB (@lem3790963 A B f b s x) (@lem3790964 B c)). Qed.
Lemma lem3790966 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3790967 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n : nat) : (term41 A B f b s x c n) = (term42 A B f b s x c n).
Proof. exact (MK_COMB (@lem3790965 A B f b s x c) (@lem3790966 n)). Qed.
Lemma lem3790968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3790969 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n : nat) : (term43 A B f b s x c n) = (term44 A B f b s x c n).
Proof. exact (MK_COMB (@lem3790968) (@lem3790967 A B f b s x c n)). Qed.
Lemma lem3790970 {A B : Type'} (a : B) (f : type1411 A B) (x : A) (c : B) : (a = (f x c)) = (a = (f x c)).
Proof. exact (eq_refl (a = (f x c))). Qed.
Lemma lem3790971 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) (x : A) (c : B) : (term45 A B b s n a f x c) = (term46 A B b s n a f x c).
Proof. exact (MK_COMB (@lem3790969 A B f b s x c n) (@lem3790970 A B a f x c)). Qed.
Lemma lem3790972 {A : Type'} (x : A) (s : A -> Prop) : (term47 A x s) = (term47 A x s).
Proof. exact (eq_refl (term47 A x s)). Qed.
Lemma lem3790973 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) (x : A) (c : B) : (term48 A B b s n a f x c) = (term49 A B b s n a f x c).
Proof. exact (MK_COMB (@lem3790972 A x s) (@lem3790971 A B b s n a f x c)). Qed.
Lemma lem3790974 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) (x : A) : (term50 A B b s n a f x) = (term51 A B b s n a f x).
Proof. exact (fun_ext (fun c : B => @lem3790973 A B b s n a f x c)). Qed.
Lemma lem3790975 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3790976 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) (x : A) : (term52 A B b s n a f x) = (term53 A B b s n a f x).
Proof. exact (MK_COMB (@lem3790975 B) (@lem3790974 A B b s n a f x)). Qed.
Lemma lem3790977 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term54 A B b s n a f) = (term55 A B b s n a f).
Proof. exact (fun_ext (fun x : A => @lem3790976 A B b s n a f x)). Qed.
Lemma lem3790978 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3790979 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term56 A B b s n a f) = (term57 A B b s n a f).
Proof. exact (MK_COMB (@lem3790978 A) (@lem3790977 A B b s n a f)). Qed.
Lemma lem3790980 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : ((term33 A B f b s a n) = (term56 A B b s n a f)) = ((term34 A B f b s a n) = (term57 A B b s n a f)).
Proof. exact (MK_COMB (@lem3790954 A B f b s a n) (@lem3790979 A B b s n a f)). Qed.
Lemma lem3790981 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) : (term58 A B b s n a) = (term59 A B b s n a).
Proof. exact (fun_ext (fun f : type1411 A B => @lem3790980 A B b s n a f)). Qed.
Lemma lem3790982 {A B : Type'} : (@all (A -> B -> B)) = (@all (A -> B -> B)).
Proof. exact (eq_refl (@all (A -> B -> B))). Qed.
Lemma lem3790983 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) : (term60 A B b s n a) = (term61 A B b s n a).
Proof. exact (MK_COMB (@lem3790982 A B) (@lem3790981 A B b s n a)). Qed.
Lemma lem3790984 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) : (term62 A B b s n) = (term63 A B b s n).
Proof. exact (fun_ext (fun a : B => @lem3790983 A B b s n a)). Qed.
Lemma lem3790985 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3790986 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) : (term64 A B b s n) = (term65 A B b s n).
Proof. exact (MK_COMB (@lem3790985 B) (@lem3790984 A B b s n)). Qed.
Lemma lem3790987 {A B : Type'} (b : B) (s : A -> Prop) : (term66 A B b s) = (term67 A B b s).
Proof. exact (fun_ext (fun n : nat => @lem3790986 A B b s n)). Qed.
Lemma lem3790988 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3790989 {A B : Type'} (b : B) (s : A -> Prop) : (term68 A B b s) = (term69 A B b s).
Proof. exact (MK_COMB (@lem3790988) (@lem3790987 A B b s)). Qed.
Lemma lem3790990 {A B : Type'} (b : B) : (term70 A B b) = (term71 A B b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3790989 A B b s)). Qed.
Lemma lem3790991 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3790992 {A B : Type'} (b : B) : (term72 A B b) = (term73 A B b).
Proof. exact (MK_COMB (@lem3790991 A) (@lem3790990 A B b)). Qed.
Lemma lem3790993 {A B : Type'} : (term74 A B) = (term75 A B).
Proof. exact (fun_ext (fun b : B => @lem3790992 A B b)). Qed.
Lemma lem3790994 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3790995 {A B : Type'} : (term76 A B) = (term77 A B).
Proof. exact (MK_COMB (@lem3790994 B) (@lem3790993 A B)). Qed.
Lemma lem3790996 {A B : Type'} : (term4 A B) = (term78 A B).
Proof. exact (MK_COMB (@lem3790939 A B) (@lem3790995 A B)). Qed.
Lemma lem3790997 {A B : Type'} : term78 A B.
Proof. exact (EQ_MP (@lem3790996 A B) (@lem3790902 A B)). Qed.

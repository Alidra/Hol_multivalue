Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_UNIQUE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSIONAL_spec.
Require Import FUN_EQ_THM_spec.
Require Import RESTRICTION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm3184714_spec.
Require Import thm3184717_spec.
Lemma lem4393916 {_83152 : Type'} : term0 _83152.
Proof. exact (EQ_MP (@lem3184717 _83152) (@lem3184714 _83152)). Qed.
Lemma lem4393917 {_83152 : Type'} (p : _83152 -> Prop) : term1 _83152 p.
Proof. exact (@lem4393916 _83152 p). Qed.
Lemma lem4393918 {_83152 : Type'} (p : _83152 -> Prop) : (term1 _83152 p) = (term2 _83152 p).
Proof. exact (eq_refl (term1 _83152 p)). Qed.
Lemma lem4393919 {_83152 : Type'} (p : _83152 -> Prop) : term2 _83152 p.
Proof. exact (EQ_MP (@lem4393918 _83152 p) (@lem4393917 _83152 p)). Qed.
Lemma lem4393920 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term3 _83152 p x.
Proof. exact (@lem4393919 _83152 p x). Qed.
Lemma lem4393921 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term3 _83152 p x) = ((term4 _83152 p x) = (p x)).
Proof. exact (eq_refl (term3 _83152 p x)). Qed.
Lemma lem4393944 {A B : Type'} (s : A -> Prop) : term5 A B s.
Proof. exact (@lem4382798 A B s). Qed.
Lemma lem4393945 {A B : Type'} (s : A -> Prop) : (term5 A B s) = ((@EXTENSIONAL A B s) = (term6 A B s)).
Proof. exact (eq_refl (term5 A B s)). Qed.
Lemma lem4393947 {A B : Type'} (s : A -> Prop) : term7 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4393948 {A B : Type'} (s : A -> Prop) : (term7 A B s) = (term8 A B s).
Proof. exact (eq_refl (term7 A B s)). Qed.
Lemma lem4393949 {A B : Type'} (s : A -> Prop) : term8 A B s.
Proof. exact (EQ_MP (@lem4393948 A B s) (@lem4393947 A B s)). Qed.
Lemma lem4393950 {A B : Type'} (s : A -> Prop) (f : A -> B) : term9 A B s f.
Proof. exact (@lem4393949 A B s f). Qed.
Lemma lem4393951 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term9 A B s f) = (term10 A B s f).
Proof. exact (eq_refl (term9 A B s f)). Qed.
Lemma lem4393952 {A B : Type'} (s : A -> Prop) (f : A -> B) : term10 A B s f.
Proof. exact (EQ_MP (@lem4393951 A B s f) (@lem4393950 A B s f)). Qed.
Lemma lem4393953 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term11 A B s f x.
Proof. exact (@lem4393952 A B s f x). Qed.
Lemma lem4393954 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term11 A B s f x) = ((@RESTRICTION A B s f x) = (term12 A B s f x)).
Proof. exact (eq_refl (term11 A B s f x)). Qed.
Lemma lem4393956 {A B : Type'} (f : A -> B) : term13 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4393957 {A B : Type'} (f : A -> B) : (term13 A B f) = (term14 A B f).
Proof. exact (eq_refl (term13 A B f)). Qed.
Lemma lem4393958 {A B : Type'} (f : A -> B) : term14 A B f.
Proof. exact (EQ_MP (@lem4393957 A B f) (@lem4393956 A B f)). Qed.
Lemma lem4393959 {A B : Type'} (f : A -> B) (g : A -> B) : term15 A B f g.
Proof. exact (@lem4393958 A B f g). Qed.
Lemma lem4393960 {A B : Type'} (f : A -> B) (g : A -> B) : (term15 A B f g) = ((f = g) = (term16 A B f g)).
Proof. exact (eq_refl (term15 A B f g)). Qed.
Lemma lem4393981 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term16 A B f g).
Proof. exact (EQ_MP (@lem4393960 A B f g) (@lem4393959 A B f g)). Qed.
Lemma lem4393982 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term16 A B f g).
Proof. exact (@lem4393981 A B f g). Qed.
Lemma lem4393983 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((@RESTRICTION A B s f) = g) = (term17 A B s f g).
Proof. exact (@lem4393982 A B (@RESTRICTION A B s f) g). Qed.
Lemma lem4393993 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term12 A B s f x).
Proof. exact (EQ_MP (@lem4393954 A B s f x) (@lem4393953 A B s f x)). Qed.
Lemma lem4393994 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term12 A B s f x).
Proof. exact (@lem4393993 A B s f x). Qed.
Lemma lem4393995 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4393996 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term18 A B s f x) = (term19 A B s f x).
Proof. exact (MK_COMB (@lem4393995 B) (@lem4393994 A B s f x)). Qed.
Lemma lem4393997 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem4393998 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : ((@RESTRICTION A B s f x) = (g x)) = ((term12 A B s f x) = (g x)).
Proof. exact (MK_COMB (@lem4393996 A B s f x) (@lem4393997 A B g x)). Qed.
Lemma lem4394003 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term20 A B s f g) = (term21 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4393998 A B s f g x)). Qed.
Lemma lem4394004 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4394005 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term17 A B s f g) = (term22 A B s f g).
Proof. exact (MK_COMB (@lem4394004 A) (@lem4394003 A B s f g)). Qed.
Lemma lem4394010 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((@RESTRICTION A B s f) = g) = (term22 A B s f g).
Proof. exact (TRANS (@lem4393983 A B s f g) (@lem4394005 A B s f g)). Qed.
Lemma lem4394011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4394012 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term23 A B s f g) = (term24 A B s f g).
Proof. exact (MK_COMB (@lem4394011) (@lem4394010 A B s f g)). Qed.
Lemma lem4394016 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term6 A B s).
Proof. exact (EQ_MP (@lem4393945 A B s) (@lem4393944 A B s)). Qed.
Lemma lem4394017 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term6 A B s).
Proof. exact (@lem4394016 A B s). Qed.
Lemma lem4394032 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem4394033 {A B : Type'} (s : A -> Prop) (g : A -> B) : (@EXTENSIONAL A B s g) = (term25 A B s g).
Proof. exact (MK_COMB (@lem4394017 A B s) (@lem4394032 A B g)). Qed.
Lemma lem4394035 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term4 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4393921 _83152 p x) (@lem4393920 _83152 p x)). Qed.
Lemma lem4394036 {A B : Type'} (p : type572 A B) (x : A -> B) : (term26 A B p x) = (p x).
Proof. exact (@lem4394035 (A -> B) p x). Qed.
Lemma lem4394037 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term27 A B s g) = (term28 A B s g).
Proof. exact (@lem4394036 A B (term29 A B s) g). Qed.
Lemma lem4394038 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term28 A B s f) = (term30 A B s f).
Proof. exact (eq_refl (term28 A B s f)). Qed.
Lemma lem4394039 {A B : Type'} (GEN_PVAR_139 : A -> B) : (@SETSPEC (A -> B) GEN_PVAR_139) = (@SETSPEC (A -> B) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (A -> B) GEN_PVAR_139)). Qed.
Lemma lem4394040 {A B : Type'} (GEN_PVAR_139 : A -> B) (s : A -> Prop) (f : A -> B) : (term31 A B GEN_PVAR_139 s f) = (term32 A B GEN_PVAR_139 s f).
Proof. exact (MK_COMB (@lem4394039 A B GEN_PVAR_139) (@lem4394038 A B s f)). Qed.
Lemma lem4394041 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4394042 {A B : Type'} (GEN_PVAR_139 : A -> B) (s : A -> Prop) (f : A -> B) : (term33 A B GEN_PVAR_139 s f) = (term34 A B GEN_PVAR_139 s f).
Proof. exact (MK_COMB (@lem4394040 A B GEN_PVAR_139 s f) (@lem4394041 A B f)). Qed.
Lemma lem4394043 {A B : Type'} (GEN_PVAR_139 : A -> B) (s : A -> Prop) : (term35 A B GEN_PVAR_139 s) = (term36 A B GEN_PVAR_139 s).
Proof. exact (fun_ext (fun f : A -> B => @lem4394042 A B GEN_PVAR_139 s f)). Qed.
Lemma lem4394044 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem4394045 {A B : Type'} (GEN_PVAR_139 : A -> B) (s : A -> Prop) : (term37 A B GEN_PVAR_139 s) = (term38 A B GEN_PVAR_139 s).
Proof. exact (MK_COMB (@lem4394044 A B) (@lem4394043 A B GEN_PVAR_139 s)). Qed.
Lemma lem4394046 {A B : Type'} (s : A -> Prop) : (term39 A B s) = (term40 A B s).
Proof. exact (fun_ext (fun GEN_PVAR_139 : A -> B => @lem4394045 A B GEN_PVAR_139 s)). Qed.
Lemma lem4394047 {A B : Type'} : (@GSPEC (A -> B)) = (@GSPEC (A -> B)).
Proof. exact (eq_refl (@GSPEC (A -> B))). Qed.
Lemma lem4394048 {A B : Type'} (s : A -> Prop) : (term41 A B s) = (term6 A B s).
Proof. exact (MK_COMB (@lem4394047 A B) (@lem4394046 A B s)). Qed.
Lemma lem4394049 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem4394050 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term27 A B s g) = (term25 A B s g).
Proof. exact (MK_COMB (@lem4394048 A B s) (@lem4394049 A B g)). Qed.
Lemma lem4394051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4394052 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term42 A B s g) = (term43 A B s g).
Proof. exact (MK_COMB (@lem4394051) (@lem4394050 A B s g)). Qed.
Lemma lem4394053 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term28 A B s g) = (term30 A B s g).
Proof. exact (eq_refl (term28 A B s g)). Qed.
Lemma lem4394054 {A B : Type'} (s : A -> Prop) (g : A -> B) : ((term27 A B s g) = (term28 A B s g)) = ((term25 A B s g) = (term30 A B s g)).
Proof. exact (MK_COMB (@lem4394052 A B s g) (@lem4394053 A B s g)). Qed.
Lemma lem4394055 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term25 A B s g) = (term30 A B s g).
Proof. exact (EQ_MP (@lem4394054 A B s g) (@lem4394037 A B s g)). Qed.
Lemma lem4394066 {A B : Type'} (s : A -> Prop) (g : A -> B) : (@EXTENSIONAL A B s g) = (term30 A B s g).
Proof. exact (TRANS (@lem4394033 A B s g) (@lem4394055 A B s g)). Qed.
Lemma lem4394067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4394068 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term44 A B s g) = (term45 A B s g).
Proof. exact (MK_COMB (@lem4394067) (@lem4394066 A B s g)). Qed.
Lemma lem4394079 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term46 A B s f g) = (term46 A B s f g).
Proof. exact (eq_refl (term46 A B s f g)). Qed.
Lemma lem4394080 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term47 A B s f g) = (term48 A B s f g).
Proof. exact (MK_COMB (@lem4394068 A B s g) (@lem4394079 A B s f g)). Qed.
Lemma lem4394083 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (((@RESTRICTION A B s f) = g) = (term47 A B s f g)) = ((term22 A B s f g) = (term48 A B s f g)).
Proof. exact (MK_COMB (@lem4394012 A B s f g) (@lem4394080 A B s f g)). Qed.
Lemma lem4394088 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term49 A B s f) = (term50 A B s f).
Proof. exact (fun_ext (fun g : A -> B => @lem4394083 A B s f g)). Qed.
Lemma lem4394089 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4394090 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term51 A B s f) = (term52 A B s f).
Proof. exact (MK_COMB (@lem4394089 A B) (@lem4394088 A B s f)). Qed.
Lemma lem4394095 {A B : Type'} (s : A -> Prop) : (term53 A B s) = (term54 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4394090 A B s f)). Qed.
Lemma lem4394096 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4394097 {A B : Type'} (s : A -> Prop) : (term55 A B s) = (term56 A B s).
Proof. exact (MK_COMB (@lem4394096 A B) (@lem4394095 A B s)). Qed.
Lemma lem4394102 {A B : Type'} : (term57 A B) = (term58 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4394097 A B s)). Qed.
Lemma lem4394103 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4394104 {A B : Type'} : (term59 A B) = (term60 A B).
Proof. exact (MK_COMB (@lem4394103 A) (@lem4394102 A B)). Qed.
Lemma lem4394109 {A B : Type'} : (term60 A B) = (term59 A B).
Proof. exact (SYM (@lem4394104 A B)). Qed.
Lemma lem4394111 (p : Prop) : p = (term61 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4394112 {A B : Type'} : (term60 A B) = (term62 A B).
Proof. exact (@lem4394111 (term60 A B)). Qed.
Lemma lem4394113 {A B : Type'} : (term62 A B) = (term60 A B).
Proof. exact (SYM (@lem4394112 A B)). Qed.
Lemma lem4394114 {A B : Type'} (h1 : term63 A B) : term63 A B.
Proof. exact (h1). Qed.
Lemma lem4394117 {A B : Type'} (h1 : term62 A B) : term62 A B.
Proof. exact (h1). Qed.
Lemma lem4394118 {A B : Type'} : term64 A B.
Proof. exact (fun h0 : term62 A B => @lem4394117 A B h0). Qed.
Lemma lem4394119 {A B : Type'} (h1 : term64 A B) : term64 A B.
Proof. exact (h1). Qed.
Lemma lem4394120 {A B : Type'} (h1 : term62 A B) : term62 A B.
Proof. exact (h1). Qed.
Lemma lem4394121 {A B : Type'} (h1 : term62 A B) (h2 : term64 A B) : term62 A B.
Proof. exact (@lem4394119 A B h2 (@lem4394120 A B h1)). Qed.
Lemma lem4394122 {A B : Type'} (h1 : term62 A B) : term65 A B.
Proof. exact (fun h0 : term64 A B => @lem4394121 A B h1 h0). Qed.
Lemma lem4394123 {A B : Type'} (h1 : term64 A B) : term64 A B.
Proof. exact (h1). Qed.
Lemma lem4394124 {A B : Type'} (h1 : term62 A B) (h2 : term64 A B) : term62 A B.
Proof. exact (@lem4394122 A B h1 (@lem4394123 A B h2)). Qed.
Lemma lem4394125 {A B : Type'} (h1 : term64 A B) : term64 A B.
Proof. exact (fun h0 : term62 A B => @lem4394124 A B h0 h1). Qed.
Lemma lem4394126 {A B : Type'} : term66 A B.
Proof. exact (fun h0 : term64 A B => @lem4394125 A B h0). Qed.
Lemma lem4394129 {A B : Type'} : term64 A B.
Proof. exact (@lem4394126 A B (@lem4394118 A B)). Qed.
Lemma lem4394130 {A B : Type'} : term64 A B.
Proof. exact (@lem4394129 A B). Qed.
Lemma lem4394132 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4394133 {A B : Type'} : (term62 A B) = (term67 A B).
Proof. exact (@lem4394132 (term63 A B)). Qed.
Lemma lem4394135 (t : Prop) : (term68 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4394136 {A B : Type'} : (term67 A B) = (term60 A B).
Proof. exact (@lem4394135 (term60 A B)). Qed.
Lemma lem4394171 {A B : Type'} : (term62 A B) = (term60 A B).
Proof. exact (TRANS (@lem4394133 A B) (@lem4394136 A B)). Qed.
Lemma lem4394176 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term69 A B s f g x) = (term69 A B s f g x).
Proof. exact (eq_refl (term69 A B s f g x)). Qed.
Lemma lem4394177 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term70 A B s f g) = (term70 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4394176 A B s f g x)). Qed.
Lemma lem4394178 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4394179 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term46 A B s f g) = (term46 A B s f g).
Proof. exact (MK_COMB (@lem4394178 A) (@lem4394177 A B s f g)). Qed.
Lemma lem4394186 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term71 A B s g x) = (term71 A B s g x).
Proof. exact (eq_refl (term71 A B s g x)). Qed.
Lemma lem4394187 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term72 A B s g) = (term72 A B s g).
Proof. exact (fun_ext (fun x : A => @lem4394186 A B s g x)). Qed.
Lemma lem4394188 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4394189 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term30 A B s g) = (term30 A B s g).
Proof. exact (MK_COMB (@lem4394188 A) (@lem4394187 A B s g)). Qed.
Lemma lem4394190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4394191 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term45 A B s g) = (term45 A B s g).
Proof. exact (MK_COMB (@lem4394190) (@lem4394189 A B s g)). Qed.
Lemma lem4394192 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term48 A B s f g) = (term48 A B s f g).
Proof. exact (MK_COMB (@lem4394191 A B s g) (@lem4394179 A B s f g)). Qed.
Lemma lem4394196 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (@IN A x s) = False.
Proof. exact (h1). Qed.
Lemma lem4394197 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4394198 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term73 A B x s) = (@COND B False).
Proof. exact (MK_COMB (@lem4394197 B) (@lem4394196 A x s h1)). Qed.
Lemma lem4394199 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4394200 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term74 A B s f x) = (term75 A B f x).
Proof. exact (MK_COMB (@lem4394198 A B x s h1) (@lem4394199 A B f x)). Qed.
Lemma lem4394201 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4394202 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term12 A B s f x) = (term76 A B f x).
Proof. exact (MK_COMB (@lem4394200 A B f x s h1) (@lem4394201 B)). Qed.
Lemma lem4394204 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4394205 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem4394204 B t1 t2). Qed.
Lemma lem4394206 {A B : Type'} (f : A -> B) (x : A) : (term76 A B f x) = (@ARB B).
Proof. exact (@lem4394205 B (f x) (@ARB B)). Qed.
Lemma lem4394207 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term12 A B s f x) = (@ARB B).
Proof. exact (TRANS (@lem4394202 A B f x s h1) (@lem4394206 A B f x)). Qed.
Lemma lem4394208 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4394209 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term19 A B s f x) = (@eq B (@ARB B)).
Proof. exact (MK_COMB (@lem4394208 B) (@lem4394207 A B f x s h1)). Qed.
Lemma lem4394210 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem4394211 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : ((term12 A B s f x) = (g x)) = ((@ARB B) = (g x)).
Proof. exact (MK_COMB (@lem4394209 A B f x s h1) (@lem4394210 A B g x)). Qed.
Lemma lem4394214 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term77 A B s f g x.
Proof. exact (fun h0 : (@IN A x s) = False => @lem4394211 A B f g x s h0). Qed.
Lemma lem4394216 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (@IN A x s) = True.
Proof. exact (h1). Qed.
Lemma lem4394217 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4394218 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term73 A B x s) = (@COND B True).
Proof. exact (MK_COMB (@lem4394217 B) (@lem4394216 A x s h1)). Qed.
Lemma lem4394219 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4394220 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term74 A B s f x) = (term78 A B f x).
Proof. exact (MK_COMB (@lem4394218 A B x s h1) (@lem4394219 A B f x)). Qed.
Lemma lem4394221 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4394222 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term12 A B s f x) = (term79 A B f x).
Proof. exact (MK_COMB (@lem4394220 A B f x s h1) (@lem4394221 B)). Qed.
Lemma lem4394224 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4394225 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem4394224 B t2 t1). Qed.
Lemma lem4394226 {A B : Type'} (f : A -> B) (x : A) : (term79 A B f x) = (f x).
Proof. exact (@lem4394225 B (@ARB B) (f x)). Qed.
Lemma lem4394227 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term12 A B s f x) = (f x).
Proof. exact (TRANS (@lem4394222 A B f x s h1) (@lem4394226 A B f x)). Qed.
Lemma lem4394228 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4394229 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term19 A B s f x) = (term80 A B f x).
Proof. exact (MK_COMB (@lem4394228 B) (@lem4394227 A B f x s h1)). Qed.
Lemma lem4394230 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem4394231 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : ((term12 A B s f x) = (g x)) = ((f x) = (g x)).
Proof. exact (MK_COMB (@lem4394229 A B f x s h1) (@lem4394230 A B g x)). Qed.
Lemma lem4394234 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term81 A B s f g x.
Proof. exact (fun h0 : (@IN A x s) = True => @lem4394231 A B f g x s h0). Qed.
Lemma lem4394235 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : term82 A B s f g x.
Proof. exact (conj (@lem4394214 A B s f g x) (@lem4394234 A B s f g x)). Qed.
Lemma lem4394237 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term83 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4394238 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : term84 A B f s g x.
Proof. exact (@lem4394237 ((term12 A B s f x) = (g x)) ((f x) = (g x)) (@IN A x s) ((@ARB B) = (g x))). Qed.
Lemma lem4394271 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : ((term12 A B s f x) = (g x)) = (term85 A B f s g x).
Proof. exact (@lem4394238 A B f s g x (@lem4394235 A B s f g x)). Qed.
Lemma lem4394272 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term21 A B s f g) = (term86 A B f s g).
Proof. exact (fun_ext (fun x : A => @lem4394271 A B f s g x)). Qed.
Lemma lem4394273 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4394274 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term22 A B s f g) = (term87 A B f s g).
Proof. exact (MK_COMB (@lem4394273 A) (@lem4394272 A B f s g)). Qed.
Lemma lem4394275 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4394276 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term24 A B s f g) = (term88 A B f s g).
Proof. exact (MK_COMB (@lem4394275) (@lem4394274 A B f s g)). Qed.
Lemma lem4394277 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term22 A B s f g) = (term48 A B s f g)) = ((term87 A B f s g) = (term48 A B s f g)).
Proof. exact (MK_COMB (@lem4394276 A B f s g) (@lem4394192 A B s f g)). Qed.
Lemma lem4394278 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term50 A B s f) = (term89 A B s f).
Proof. exact (fun_ext (fun g : A -> B => @lem4394277 A B s f g)). Qed.
Lemma lem4394279 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4394280 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term52 A B s f) = (term90 A B s f).
Proof. exact (MK_COMB (@lem4394279 A B) (@lem4394278 A B s f)). Qed.
Lemma lem4394281 {A B : Type'} (s : A -> Prop) : (term54 A B s) = (term91 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4394280 A B s f)). Qed.
Lemma lem4394282 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4394283 {A B : Type'} (s : A -> Prop) : (term56 A B s) = (term92 A B s).
Proof. exact (MK_COMB (@lem4394282 A B) (@lem4394281 A B s)). Qed.
Lemma lem4394284 {A B : Type'} : (term58 A B) = (term93 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4394283 A B s)). Qed.
Lemma lem4394285 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4394286 {A B : Type'} : (term60 A B) = (term94 A B).
Proof. exact (MK_COMB (@lem4394285 A) (@lem4394284 A B)). Qed.
Lemma lem4394337 {A B : Type'} : (term62 A B) = (term94 A B).
Proof. exact (TRANS (@lem4394171 A B) (@lem4394286 A B)). Qed.
Lemma lem4394338 {A B : Type'} : (term94 A B) = (term62 A B).
Proof. exact (SYM (@lem4394337 A B)). Qed.
Lemma lem4394340 (p : Prop) : p = (term61 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4394341 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term87 A B f s g) = (term48 A B s f g)) = (term95 A B s f g).
Proof. exact (@lem4394340 ((term87 A B f s g) = (term48 A B s f g))). Qed.
Lemma lem4394342 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term95 A B s f g) = ((term87 A B f s g) = (term48 A B s f g)).
Proof. exact (SYM (@lem4394341 A B s f g)). Qed.
Lemma lem4394343 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term96 A B s f g) : term96 A B s f g.
Proof. exact (h1). Qed.
Lemma lem4394347 {A : Type'} (x : A) (s : A -> Prop) : (term97 A x s) = (@IN A x s).
Proof. exact (@lem16933 (@IN A x s)). Qed.
Lemma lem4394348 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term98 A B f g x) = (term98 A B f g x).
Proof. exact (eq_refl (term98 A B f g x)). Qed.
Lemma lem4394350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4394351 {A : Type'} (x : A) (s : A -> Prop) : (term99 A x s) = (term100 A x s).
Proof. exact (MK_COMB (@lem4394350) (@lem4394347 A x s)). Qed.
Lemma lem4394352 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term101 A B s f g x) = (term102 A B s f g x).
Proof. exact (MK_COMB (@lem4394351 A x s) (@lem4394348 A B f g x)). Qed.
Lemma lem4394353 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term103 A B s f g x) = (term101 A B s f g x).
Proof. exact (@lem17160 (term104 A x s) ((f x) = (g x))). Qed.
Lemma lem4394354 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term103 A B s f g x) = (term102 A B s f g x).
Proof. exact (TRANS (@lem4394353 A B s f g x) (@lem4394352 A B s f g x)). Qed.
Lemma lem4394366 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term105 A B s g x) = (term106 A B s g x).
Proof. exact (@lem17160 (@IN A x s) ((@ARB B) = (g x))). Qed.
Lemma lem4394370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4394371 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term107 A B s f g x) = (term108 A B s f g x).
Proof. exact (MK_COMB (@lem4394370) (@lem4394354 A B s f g x)). Qed.
Lemma lem4394372 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term109 A B f s g x) = (term110 A B f s g x).
Proof. exact (MK_COMB (@lem4394371 A B s f g x) (@lem4394366 A B s g x)). Qed.
Lemma lem4394373 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term111 A B f s g x) = (term109 A B f s g x).
Proof. exact (@lem17045 (term112 A B s f g x) (term113 A B s g x)). Qed.
Lemma lem4394374 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term111 A B f s g x) = (term110 A B f s g x).
Proof. exact (TRANS (@lem4394373 A B f s g x) (@lem4394372 A B f s g x)). Qed.
Lemma lem4394377 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term85 A B f s g x) = (term85 A B f s g x).
Proof. exact (eq_refl (term85 A B f s g x)). Qed.
Lemma lem4394378 {A : Type'} (P : A -> Prop) : (term114 A P) = (term115 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4394379 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term116 A B f s g) = (term117 A B f s g).
Proof. exact (@lem4394378 A (term86 A B f s g)). Qed.
Lemma lem4394380 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term118 A B f s g x) = (term85 A B f s g x).
Proof. exact (eq_refl (term118 A B f s g x)). Qed.
Lemma lem4394381 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4394382 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term119 A B f s g x) = (term111 A B f s g x).
Proof. exact (MK_COMB (@lem4394381) (@lem4394380 A B f s g x)). Qed.
Lemma lem4394383 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term119 A B f s g x) = (term110 A B f s g x).
Proof. exact (TRANS (@lem4394382 A B f s g x) (@lem4394374 A B f s g x)). Qed.
Lemma lem4394384 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term120 A B f s g) = (term121 A B f s g).
Proof. exact (fun_ext (fun x : A => @lem4394383 A B f s g x)). Qed.
Lemma lem4394385 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394386 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term117 A B f s g) = (term122 A B f s g).
Proof. exact (MK_COMB (@lem4394385 A) (@lem4394384 A B f s g)). Qed.
Lemma lem4394387 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term116 A B f s g) = (term122 A B f s g).
Proof. exact (TRANS (@lem4394379 A B f s g) (@lem4394386 A B f s g)). Qed.
Lemma lem4394388 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term86 A B f s g) = (term86 A B f s g).
Proof. exact (fun_ext (fun x : A => @lem4394377 A B f s g x)). Qed.
Lemma lem4394389 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4394390 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term87 A B f s g) = (term87 A B f s g).
Proof. exact (MK_COMB (@lem4394389 A) (@lem4394388 A B f s g)). Qed.
Lemma lem4394394 {A : Type'} (x : A) (s : A -> Prop) : (term97 A x s) = (@IN A x s).
Proof. exact (@lem16933 (@IN A x s)). Qed.
Lemma lem4394396 {A B : Type'} (g : A -> B) (x : A) : ((g x) = (@ARB B)) = ((g x) = (@ARB B)).
Proof. exact (eq_refl ((g x) = (@ARB B))). Qed.
Lemma lem4394401 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term123 A B s g x) = (term124 A B s g x).
Proof. exact (@lem17362 (term104 A x s) ((g x) = (@ARB B))). Qed.
Lemma lem4394402 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4394403 {A : Type'} (x : A) (s : A -> Prop) : (term125 A x s) = (term126 A x s).
Proof. exact (MK_COMB (@lem4394402) (@lem4394394 A x s)). Qed.
Lemma lem4394404 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term127 A B s g x) = (term128 A B s g x).
Proof. exact (MK_COMB (@lem4394403 A x s) (@lem4394396 A B g x)). Qed.
Lemma lem4394405 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term71 A B s g x) = (term127 A B s g x).
Proof. exact (@lem17265 (term104 A x s) ((g x) = (@ARB B))). Qed.
Lemma lem4394406 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term71 A B s g x) = (term128 A B s g x).
Proof. exact (TRANS (@lem4394405 A B s g x) (@lem4394404 A B s g x)). Qed.
Lemma lem4394407 {A : Type'} (P : A -> Prop) : (term114 A P) = (term115 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4394408 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term129 A B s g) = (term130 A B s g).
Proof. exact (@lem4394407 A (term72 A B s g)). Qed.
Lemma lem4394409 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term131 A B s g x) = (term71 A B s g x).
Proof. exact (eq_refl (term131 A B s g x)). Qed.
Lemma lem4394410 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4394411 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term132 A B s g x) = (term123 A B s g x).
Proof. exact (MK_COMB (@lem4394410) (@lem4394409 A B s g x)). Qed.
Lemma lem4394412 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term132 A B s g x) = (term124 A B s g x).
Proof. exact (TRANS (@lem4394411 A B s g x) (@lem4394401 A B s g x)). Qed.
Lemma lem4394413 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term133 A B s g) = (term134 A B s g).
Proof. exact (fun_ext (fun x : A => @lem4394412 A B s g x)). Qed.
Lemma lem4394414 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394415 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term130 A B s g) = (term135 A B s g).
Proof. exact (MK_COMB (@lem4394414 A) (@lem4394413 A B s g)). Qed.
Lemma lem4394416 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term129 A B s g) = (term135 A B s g).
Proof. exact (TRANS (@lem4394408 A B s g) (@lem4394415 A B s g)). Qed.
Lemma lem4394417 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term72 A B s g) = (term136 A B s g).
Proof. exact (fun_ext (fun x : A => @lem4394406 A B s g x)). Qed.
Lemma lem4394418 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4394419 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term30 A B s g) = (term137 A B s g).
Proof. exact (MK_COMB (@lem4394418 A) (@lem4394417 A B s g)). Qed.
Lemma lem4394428 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term138 A B s f g x) = (term102 A B s f g x).
Proof. exact (@lem17362 (@IN A x s) ((f x) = (g x))). Qed.
Lemma lem4394433 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term69 A B s f g x) = (term112 A B s f g x).
Proof. exact (@lem17265 (@IN A x s) ((f x) = (g x))). Qed.
Lemma lem4394434 {A : Type'} (P : A -> Prop) : (term114 A P) = (term115 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4394435 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term139 A B s f g) = (term140 A B s f g).
Proof. exact (@lem4394434 A (term70 A B s f g)). Qed.
Lemma lem4394436 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term141 A B s f g x) = (term69 A B s f g x).
Proof. exact (eq_refl (term141 A B s f g x)). Qed.
Lemma lem4394437 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4394438 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term142 A B s f g x) = (term138 A B s f g x).
Proof. exact (MK_COMB (@lem4394437) (@lem4394436 A B s f g x)). Qed.
Lemma lem4394439 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term142 A B s f g x) = (term102 A B s f g x).
Proof. exact (TRANS (@lem4394438 A B s f g x) (@lem4394428 A B s f g x)). Qed.
Lemma lem4394440 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term143 A B s f g) = (term144 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4394439 A B s f g x)). Qed.
Lemma lem4394441 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394442 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term140 A B s f g) = (term145 A B s f g).
Proof. exact (MK_COMB (@lem4394441 A) (@lem4394440 A B s f g)). Qed.
Lemma lem4394443 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term139 A B s f g) = (term145 A B s f g).
Proof. exact (TRANS (@lem4394435 A B s f g) (@lem4394442 A B s f g)). Qed.
Lemma lem4394444 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term70 A B s f g) = (term146 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4394433 A B s f g x)). Qed.
Lemma lem4394445 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4394446 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term46 A B s f g) = (term147 A B s f g).
Proof. exact (MK_COMB (@lem4394445 A) (@lem4394444 A B s f g)). Qed.
Lemma lem4394447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4394448 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term148 A B s g) = (term149 A B s g).
Proof. exact (MK_COMB (@lem4394447) (@lem4394416 A B s g)). Qed.
Lemma lem4394449 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term150 A B s f g) = (term151 A B s f g).
Proof. exact (MK_COMB (@lem4394448 A B s g) (@lem4394443 A B s f g)). Qed.
Lemma lem4394450 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term152 A B s f g) = (term150 A B s f g).
Proof. exact (@lem17045 (term30 A B s g) (term46 A B s f g)). Qed.
Lemma lem4394451 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term152 A B s f g) = (term151 A B s f g).
Proof. exact (TRANS (@lem4394450 A B s f g) (@lem4394449 A B s f g)). Qed.
Lemma lem4394452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4394453 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term45 A B s g) = (term153 A B s g).
Proof. exact (MK_COMB (@lem4394452) (@lem4394419 A B s g)). Qed.
Lemma lem4394454 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term48 A B s f g) = (term154 A B s f g).
Proof. exact (MK_COMB (@lem4394453 A B s g) (@lem4394446 A B s f g)). Qed.
Lemma lem4394455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4394456 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term155 A B f s g) = (term156 A B f s g).
Proof. exact (MK_COMB (@lem4394455) (@lem4394387 A B f s g)). Qed.
Lemma lem4394457 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term157 A B s f g) = (term158 A B s f g).
Proof. exact (MK_COMB (@lem4394456 A B f s g) (@lem4394454 A B s f g)). Qed.
Lemma lem4394458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4394459 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term159 A B f s g) = (term159 A B f s g).
Proof. exact (MK_COMB (@lem4394458) (@lem4394390 A B f s g)). Qed.
Lemma lem4394460 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term160 A B s f g) = (term161 A B s f g).
Proof. exact (MK_COMB (@lem4394459 A B f s g) (@lem4394451 A B s f g)). Qed.
Lemma lem4394461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4394462 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term162 A B s f g) = (term163 A B s f g).
Proof. exact (MK_COMB (@lem4394461) (@lem4394460 A B s f g)). Qed.
Lemma lem4394463 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term164 A B s f g) = (term165 A B s f g).
Proof. exact (MK_COMB (@lem4394462 A B s f g) (@lem4394457 A B s f g)). Qed.
Lemma lem4394464 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term96 A B s f g) = (term164 A B s f g).
Proof. exact (@lem17646 (term87 A B f s g) (term48 A B s f g)). Qed.
Lemma lem4394465 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term96 A B s f g) = (term165 A B s f g).
Proof. exact (TRANS (@lem4394464 A B s f g) (@lem4394463 A B s f g)). Qed.
Lemma lem4394467 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4394468 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (@lem4394467 A P Q). Qed.
Lemma lem4394469 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term168 A B f s g) = (term169 A B f s g).
Proof. exact (@lem4394468 A (term146 A B s f g) (term170 A B s g)). Qed.
Lemma lem4394470 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term171 A B s f g x) = (term112 A B s f g x).
Proof. exact (eq_refl (term171 A B s f g x)). Qed.
Lemma lem4394471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4394472 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term172 A B s f g x) = (term173 A B s f g x).
Proof. exact (MK_COMB (@lem4394471) (@lem4394470 A B s f g x)). Qed.
Lemma lem4394473 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term174 A B s g x) = (term113 A B s g x).
Proof. exact (eq_refl (term174 A B s g x)). Qed.
Lemma lem4394474 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term175 A B f s g x) = (term85 A B f s g x).
Proof. exact (MK_COMB (@lem4394472 A B s f g x) (@lem4394473 A B s g x)). Qed.
Lemma lem4394475 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term176 A B f s g) = (term86 A B f s g).
Proof. exact (fun_ext (fun x : A => @lem4394474 A B f s g x)). Qed.
Lemma lem4394476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4394477 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term168 A B f s g) = (term87 A B f s g).
Proof. exact (MK_COMB (@lem4394476 A) (@lem4394475 A B f s g)). Qed.
Lemma lem4394478 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4394479 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term177 A B f s g) = (term88 A B f s g).
Proof. exact (MK_COMB (@lem4394478) (@lem4394477 A B f s g)). Qed.
Lemma lem4394480 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term171 A B s f g x) = (term112 A B s f g x).
Proof. exact (eq_refl (term171 A B s f g x)). Qed.
Lemma lem4394481 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term178 A B s f g) = (term146 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4394480 A B s f g x)). Qed.
Lemma lem4394482 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4394483 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term179 A B s f g) = (term147 A B s f g).
Proof. exact (MK_COMB (@lem4394482 A) (@lem4394481 A B s f g)). Qed.
Lemma lem4394484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4394485 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term180 A B s f g) = (term181 A B s f g).
Proof. exact (MK_COMB (@lem4394484) (@lem4394483 A B s f g)). Qed.
Lemma lem4394486 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term174 A B s g x) = (term113 A B s g x).
Proof. exact (eq_refl (term174 A B s g x)). Qed.
Lemma lem4394487 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term182 A B s g) = (term170 A B s g).
Proof. exact (fun_ext (fun x : A => @lem4394486 A B s g x)). Qed.
Lemma lem4394488 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4394489 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term183 A B s g) = (term184 A B s g).
Proof. exact (MK_COMB (@lem4394488 A) (@lem4394487 A B s g)). Qed.
Lemma lem4394490 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term169 A B f s g) = (term185 A B f s g).
Proof. exact (MK_COMB (@lem4394485 A B s f g) (@lem4394489 A B s g)). Qed.
Lemma lem4394491 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : ((term168 A B f s g) = (term169 A B f s g)) = ((term87 A B f s g) = (term185 A B f s g)).
Proof. exact (MK_COMB (@lem4394479 A B f s g) (@lem4394490 A B f s g)). Qed.
Lemma lem4394492 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term87 A B f s g) = (term185 A B f s g).
Proof. exact (EQ_MP (@lem4394491 A B f s g) (@lem4394469 A B f s g)). Qed.
Lemma lem4394589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4394590 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term159 A B f s g) = (term186 A B f s g).
Proof. exact (MK_COMB (@lem4394589) (@lem4394492 A B f s g)). Qed.
Lemma lem4394687 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term151 A B s f g) = (term151 A B s f g).
Proof. exact (eq_refl (term151 A B s f g)). Qed.
Lemma lem4394688 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term161 A B s f g) = (term187 A B s f g).
Proof. exact (MK_COMB (@lem4394590 A B f s g) (@lem4394687 A B s f g)). Qed.
Lemma lem4394689 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4394690 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term163 A B s f g) = (term188 A B s f g).
Proof. exact (MK_COMB (@lem4394689) (@lem4394688 A B s f g)). Qed.
Lemma lem4394692 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term189 A P Q) = (term190 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4394693 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term189 A P Q) = (term190 A P Q).
Proof. exact (@lem4394692 A P Q). Qed.
Lemma lem4394694 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term191 A B f s g) = (term192 A B f s g).
Proof. exact (@lem4394693 A (term144 A B s f g) (term193 A B s g)). Qed.
Lemma lem4394695 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term194 A B s f g x) = (term102 A B s f g x).
Proof. exact (eq_refl (term194 A B s f g x)). Qed.
Lemma lem4394696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4394697 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term195 A B s f g x) = (term108 A B s f g x).
Proof. exact (MK_COMB (@lem4394696) (@lem4394695 A B s f g x)). Qed.
Lemma lem4394698 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term196 A B s g x) = (term106 A B s g x).
Proof. exact (eq_refl (term196 A B s g x)). Qed.
Lemma lem4394699 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term197 A B f s g x) = (term110 A B f s g x).
Proof. exact (MK_COMB (@lem4394697 A B s f g x) (@lem4394698 A B s g x)). Qed.
Lemma lem4394700 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term198 A B f s g) = (term121 A B f s g).
Proof. exact (fun_ext (fun x : A => @lem4394699 A B f s g x)). Qed.
Lemma lem4394701 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394702 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term191 A B f s g) = (term122 A B f s g).
Proof. exact (MK_COMB (@lem4394701 A) (@lem4394700 A B f s g)). Qed.
Lemma lem4394703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4394704 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term199 A B f s g) = (term200 A B f s g).
Proof. exact (MK_COMB (@lem4394703) (@lem4394702 A B f s g)). Qed.
Lemma lem4394705 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term194 A B s f g x) = (term102 A B s f g x).
Proof. exact (eq_refl (term194 A B s f g x)). Qed.
Lemma lem4394706 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term201 A B s f g) = (term144 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4394705 A B s f g x)). Qed.
Lemma lem4394707 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394708 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term202 A B s f g) = (term145 A B s f g).
Proof. exact (MK_COMB (@lem4394707 A) (@lem4394706 A B s f g)). Qed.
Lemma lem4394709 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4394710 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term203 A B s f g) = (term204 A B s f g).
Proof. exact (MK_COMB (@lem4394709) (@lem4394708 A B s f g)). Qed.
Lemma lem4394711 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term196 A B s g x) = (term106 A B s g x).
Proof. exact (eq_refl (term196 A B s g x)). Qed.
Lemma lem4394712 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term205 A B s g) = (term193 A B s g).
Proof. exact (fun_ext (fun x : A => @lem4394711 A B s g x)). Qed.
Lemma lem4394713 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394714 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term206 A B s g) = (term207 A B s g).
Proof. exact (MK_COMB (@lem4394713 A) (@lem4394712 A B s g)). Qed.
Lemma lem4394715 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term192 A B f s g) = (term208 A B f s g).
Proof. exact (MK_COMB (@lem4394710 A B s f g) (@lem4394714 A B s g)). Qed.
Lemma lem4394716 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : ((term191 A B f s g) = (term192 A B f s g)) = ((term122 A B f s g) = (term208 A B f s g)).
Proof. exact (MK_COMB (@lem4394704 A B f s g) (@lem4394715 A B f s g)). Qed.
Lemma lem4394717 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term122 A B f s g) = (term208 A B f s g).
Proof. exact (EQ_MP (@lem4394716 A B f s g) (@lem4394694 A B f s g)). Qed.
Lemma lem4394814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4394815 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term156 A B f s g) = (term209 A B f s g).
Proof. exact (MK_COMB (@lem4394814) (@lem4394717 A B f s g)). Qed.
Lemma lem4394912 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term154 A B s f g) = (term154 A B s f g).
Proof. exact (eq_refl (term154 A B s f g)). Qed.
Lemma lem4394913 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term158 A B s f g) = (term210 A B s f g).
Proof. exact (MK_COMB (@lem4394815 A B f s g) (@lem4394912 A B s f g)). Qed.
Lemma lem4394914 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term165 A B s f g) = (term211 A B s f g).
Proof. exact (MK_COMB (@lem4394690 A B s f g) (@lem4394913 A B s f g)). Qed.
Lemma lem4394916 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term190 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4394917 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term190 A P Q) = (term189 A P Q).
Proof. exact (@lem4394916 A P Q). Qed.
Lemma lem4394918 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term212 A B s f g) = (term213 A B s f g).
Proof. exact (@lem4394917 A (term134 A B s g) (term144 A B s f g)). Qed.
Lemma lem4394919 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term214 A B s g x) = (term124 A B s g x).
Proof. exact (eq_refl (term214 A B s g x)). Qed.
Lemma lem4394920 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term215 A B s g) = (term134 A B s g).
Proof. exact (fun_ext (fun x : A => @lem4394919 A B s g x)). Qed.
Lemma lem4394921 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394922 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term216 A B s g) = (term135 A B s g).
Proof. exact (MK_COMB (@lem4394921 A) (@lem4394920 A B s g)). Qed.
Lemma lem4394923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4394924 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term217 A B s g) = (term149 A B s g).
Proof. exact (MK_COMB (@lem4394923) (@lem4394922 A B s g)). Qed.
Lemma lem4394925 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term194 A B s f g x) = (term102 A B s f g x).
Proof. exact (eq_refl (term194 A B s f g x)). Qed.
Lemma lem4394926 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term201 A B s f g) = (term144 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4394925 A B s f g x)). Qed.
Lemma lem4394927 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394928 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term202 A B s f g) = (term145 A B s f g).
Proof. exact (MK_COMB (@lem4394927 A) (@lem4394926 A B s f g)). Qed.
Lemma lem4394929 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term212 A B s f g) = (term151 A B s f g).
Proof. exact (MK_COMB (@lem4394924 A B s g) (@lem4394928 A B s f g)). Qed.
Lemma lem4394930 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4394931 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term218 A B s f g) = (term219 A B s f g).
Proof. exact (MK_COMB (@lem4394930) (@lem4394929 A B s f g)). Qed.
Lemma lem4394932 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term214 A B s g x) = (term124 A B s g x).
Proof. exact (eq_refl (term214 A B s g x)). Qed.
Lemma lem4394933 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4394934 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term220 A B s g x) = (term221 A B s g x).
Proof. exact (MK_COMB (@lem4394933) (@lem4394932 A B s g x)). Qed.
Lemma lem4394935 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term194 A B s f g x) = (term102 A B s f g x).
Proof. exact (eq_refl (term194 A B s f g x)). Qed.
Lemma lem4394936 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term222 A B s f g x) = (term223 A B s f g x).
Proof. exact (MK_COMB (@lem4394934 A B s g x) (@lem4394935 A B s f g x)). Qed.
Lemma lem4394937 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term224 A B s f g) = (term225 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4394936 A B s f g x)). Qed.
Lemma lem4394938 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394939 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term213 A B s f g) = (term226 A B s f g).
Proof. exact (MK_COMB (@lem4394938 A) (@lem4394937 A B s f g)). Qed.
Lemma lem4394940 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term212 A B s f g) = (term213 A B s f g)) = ((term151 A B s f g) = (term226 A B s f g)).
Proof. exact (MK_COMB (@lem4394931 A B s f g) (@lem4394939 A B s f g)). Qed.
Lemma lem4394941 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term151 A B s f g) = (term226 A B s f g).
Proof. exact (EQ_MP (@lem4394940 A B s f g) (@lem4394918 A B s f g)). Qed.
Lemma lem4394942 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term186 A B f s g) = (term186 A B f s g).
Proof. exact (eq_refl (term186 A B f s g)). Qed.
Lemma lem4394943 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term187 A B s f g) = (term227 A B s f g).
Proof. exact (MK_COMB (@lem4394942 A B f s g) (@lem4394941 A B s f g)). Qed.
Lemma lem4394945 {A : Type'} (P : Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4394946 {A : Type'} (P : Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (@lem4394945 A P Q). Qed.
Lemma lem4394947 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term230 A B s f g) = (term231 A B s f g).
Proof. exact (@lem4394946 A (term185 A B f s g) (term225 A B s f g)). Qed.
Lemma lem4394948 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term232 A B s f g x) = (term223 A B s f g x).
Proof. exact (eq_refl (term232 A B s f g x)). Qed.
Lemma lem4394949 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term233 A B s f g) = (term225 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4394948 A B s f g x)). Qed.
Lemma lem4394950 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394951 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term234 A B s f g) = (term226 A B s f g).
Proof. exact (MK_COMB (@lem4394950 A) (@lem4394949 A B s f g)). Qed.
Lemma lem4394952 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term186 A B f s g) = (term186 A B f s g).
Proof. exact (eq_refl (term186 A B f s g)). Qed.
Lemma lem4394953 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term230 A B s f g) = (term227 A B s f g).
Proof. exact (MK_COMB (@lem4394952 A B f s g) (@lem4394951 A B s f g)). Qed.
Lemma lem4394954 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4394955 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term235 A B s f g) = (term236 A B s f g).
Proof. exact (MK_COMB (@lem4394954) (@lem4394953 A B s f g)). Qed.
Lemma lem4394956 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term232 A B s f g x) = (term223 A B s f g x).
Proof. exact (eq_refl (term232 A B s f g x)). Qed.
Lemma lem4394957 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term186 A B f s g) = (term186 A B f s g).
Proof. exact (eq_refl (term186 A B f s g)). Qed.
Lemma lem4394958 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term237 A B s f g x) = (term238 A B s f g x).
Proof. exact (MK_COMB (@lem4394957 A B f s g) (@lem4394956 A B s f g x)). Qed.
Lemma lem4394959 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term239 A B s f g) = (term240 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4394958 A B s f g x)). Qed.
Lemma lem4394960 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394961 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term231 A B s f g) = (term241 A B s f g).
Proof. exact (MK_COMB (@lem4394960 A) (@lem4394959 A B s f g)). Qed.
Lemma lem4394962 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term230 A B s f g) = (term231 A B s f g)) = ((term227 A B s f g) = (term241 A B s f g)).
Proof. exact (MK_COMB (@lem4394955 A B s f g) (@lem4394961 A B s f g)). Qed.
Lemma lem4394963 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term227 A B s f g) = (term241 A B s f g).
Proof. exact (EQ_MP (@lem4394962 A B s f g) (@lem4394947 A B s f g)). Qed.
Lemma lem4394964 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term187 A B s f g) = (term241 A B s f g).
Proof. exact (TRANS (@lem4394943 A B s f g) (@lem4394963 A B s f g)). Qed.
Lemma lem4394965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4394966 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term188 A B s f g) = (term242 A B s f g).
Proof. exact (MK_COMB (@lem4394965) (@lem4394964 A B s f g)). Qed.
Lemma lem4394968 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term190 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4394969 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term190 A P Q) = (term189 A P Q).
Proof. exact (@lem4394968 A P Q). Qed.
Lemma lem4394970 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term192 A B f s g) = (term191 A B f s g).
Proof. exact (@lem4394969 A (term144 A B s f g) (term193 A B s g)). Qed.
Lemma lem4394971 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term194 A B s f g x) = (term102 A B s f g x).
Proof. exact (eq_refl (term194 A B s f g x)). Qed.
Lemma lem4394972 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term201 A B s f g) = (term144 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4394971 A B s f g x)). Qed.
Lemma lem4394973 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394974 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term202 A B s f g) = (term145 A B s f g).
Proof. exact (MK_COMB (@lem4394973 A) (@lem4394972 A B s f g)). Qed.
Lemma lem4394975 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4394976 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term203 A B s f g) = (term204 A B s f g).
Proof. exact (MK_COMB (@lem4394975) (@lem4394974 A B s f g)). Qed.
Lemma lem4394977 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term196 A B s g x) = (term106 A B s g x).
Proof. exact (eq_refl (term196 A B s g x)). Qed.
Lemma lem4394978 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term205 A B s g) = (term193 A B s g).
Proof. exact (fun_ext (fun x : A => @lem4394977 A B s g x)). Qed.
Lemma lem4394979 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394980 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term206 A B s g) = (term207 A B s g).
Proof. exact (MK_COMB (@lem4394979 A) (@lem4394978 A B s g)). Qed.
Lemma lem4394981 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term192 A B f s g) = (term208 A B f s g).
Proof. exact (MK_COMB (@lem4394976 A B s f g) (@lem4394980 A B s g)). Qed.
Lemma lem4394982 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4394983 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term243 A B f s g) = (term244 A B f s g).
Proof. exact (MK_COMB (@lem4394982) (@lem4394981 A B f s g)). Qed.
Lemma lem4394984 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term194 A B s f g x) = (term102 A B s f g x).
Proof. exact (eq_refl (term194 A B s f g x)). Qed.
Lemma lem4394985 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4394986 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term195 A B s f g x) = (term108 A B s f g x).
Proof. exact (MK_COMB (@lem4394985) (@lem4394984 A B s f g x)). Qed.
Lemma lem4394987 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term196 A B s g x) = (term106 A B s g x).
Proof. exact (eq_refl (term196 A B s g x)). Qed.
Lemma lem4394988 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term197 A B f s g x) = (term110 A B f s g x).
Proof. exact (MK_COMB (@lem4394986 A B s f g x) (@lem4394987 A B s g x)). Qed.
Lemma lem4394989 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term198 A B f s g) = (term121 A B f s g).
Proof. exact (fun_ext (fun x : A => @lem4394988 A B f s g x)). Qed.
Lemma lem4394990 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4394991 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term191 A B f s g) = (term122 A B f s g).
Proof. exact (MK_COMB (@lem4394990 A) (@lem4394989 A B f s g)). Qed.
Lemma lem4394992 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : ((term192 A B f s g) = (term191 A B f s g)) = ((term208 A B f s g) = (term122 A B f s g)).
Proof. exact (MK_COMB (@lem4394983 A B f s g) (@lem4394991 A B f s g)). Qed.
Lemma lem4394993 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term208 A B f s g) = (term122 A B f s g).
Proof. exact (EQ_MP (@lem4394992 A B f s g) (@lem4394970 A B f s g)). Qed.
Lemma lem4394994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4394995 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term209 A B f s g) = (term156 A B f s g).
Proof. exact (MK_COMB (@lem4394994) (@lem4394993 A B f s g)). Qed.
Lemma lem4394996 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term154 A B s f g) = (term154 A B s f g).
Proof. exact (eq_refl (term154 A B s f g)). Qed.
Lemma lem4394997 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term210 A B s f g) = (term158 A B s f g).
Proof. exact (MK_COMB (@lem4394995 A B f s g) (@lem4394996 A B s f g)). Qed.
Lemma lem4394999 {A : Type'} (P : A -> Prop) (Q : Prop) : (term245 A P Q) = (term246 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4395000 {A : Type'} (P : A -> Prop) (Q : Prop) : (term245 A P Q) = (term246 A P Q).
Proof. exact (@lem4394999 A P Q). Qed.
Lemma lem4395001 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term247 A B s f g) = (term248 A B s f g).
Proof. exact (@lem4395000 A (term121 A B f s g) (term154 A B s f g)). Qed.
Lemma lem4395002 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term249 A B f s g x) = (term110 A B f s g x).
Proof. exact (eq_refl (term249 A B f s g x)). Qed.
Lemma lem4395003 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term250 A B f s g) = (term121 A B f s g).
Proof. exact (fun_ext (fun x : A => @lem4395002 A B f s g x)). Qed.
Lemma lem4395004 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4395005 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term251 A B f s g) = (term122 A B f s g).
Proof. exact (MK_COMB (@lem4395004 A) (@lem4395003 A B f s g)). Qed.
Lemma lem4395006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4395007 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term252 A B f s g) = (term156 A B f s g).
Proof. exact (MK_COMB (@lem4395006) (@lem4395005 A B f s g)). Qed.
Lemma lem4395008 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term154 A B s f g) = (term154 A B s f g).
Proof. exact (eq_refl (term154 A B s f g)). Qed.
Lemma lem4395009 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term247 A B s f g) = (term158 A B s f g).
Proof. exact (MK_COMB (@lem4395007 A B f s g) (@lem4395008 A B s f g)). Qed.
Lemma lem4395010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4395011 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term253 A B s f g) = (term254 A B s f g).
Proof. exact (MK_COMB (@lem4395010) (@lem4395009 A B s f g)). Qed.
Lemma lem4395012 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term249 A B f s g x) = (term110 A B f s g x).
Proof. exact (eq_refl (term249 A B f s g x)). Qed.
Lemma lem4395013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4395014 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term255 A B f s g x) = (term256 A B f s g x).
Proof. exact (MK_COMB (@lem4395013) (@lem4395012 A B f s g x)). Qed.
Lemma lem4395015 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term154 A B s f g) = (term154 A B s f g).
Proof. exact (eq_refl (term154 A B s f g)). Qed.
Lemma lem4395016 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term257 A B x s f g) = (term258 A B x s f g).
Proof. exact (MK_COMB (@lem4395014 A B f s g x) (@lem4395015 A B s f g)). Qed.
Lemma lem4395017 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term259 A B s f g) = (term260 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4395016 A B x s f g)). Qed.
Lemma lem4395018 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4395019 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term248 A B s f g) = (term261 A B s f g).
Proof. exact (MK_COMB (@lem4395018 A) (@lem4395017 A B s f g)). Qed.
Lemma lem4395020 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term247 A B s f g) = (term248 A B s f g)) = ((term158 A B s f g) = (term261 A B s f g)).
Proof. exact (MK_COMB (@lem4395011 A B s f g) (@lem4395019 A B s f g)). Qed.
Lemma lem4395021 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term158 A B s f g) = (term261 A B s f g).
Proof. exact (EQ_MP (@lem4395020 A B s f g) (@lem4395001 A B s f g)). Qed.
Lemma lem4395022 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term210 A B s f g) = (term261 A B s f g).
Proof. exact (TRANS (@lem4394997 A B s f g) (@lem4395021 A B s f g)). Qed.
Lemma lem4395023 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term211 A B s f g) = (term262 A B s f g).
Proof. exact (MK_COMB (@lem4394966 A B s f g) (@lem4395022 A B s f g)). Qed.
Lemma lem4395025 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term190 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4395026 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term190 A P Q) = (term189 A P Q).
Proof. exact (@lem4395025 A P Q). Qed.
Lemma lem4395027 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term263 A B s f g) = (term264 A B s f g).
Proof. exact (@lem4395026 A (term240 A B s f g) (term260 A B s f g)). Qed.
Lemma lem4395028 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term265 A B s f g x) = (term238 A B s f g x).
Proof. exact (eq_refl (term265 A B s f g x)). Qed.
Lemma lem4395029 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term266 A B s f g) = (term240 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4395028 A B s f g x)). Qed.
Lemma lem4395030 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4395031 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term267 A B s f g) = (term241 A B s f g).
Proof. exact (MK_COMB (@lem4395030 A) (@lem4395029 A B s f g)). Qed.
Lemma lem4395032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4395033 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term268 A B s f g) = (term242 A B s f g).
Proof. exact (MK_COMB (@lem4395032) (@lem4395031 A B s f g)). Qed.
Lemma lem4395034 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term269 A B s f g x) = (term258 A B x s f g).
Proof. exact (eq_refl (term269 A B s f g x)). Qed.
Lemma lem4395035 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term270 A B s f g) = (term260 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4395034 A B x s f g)). Qed.
Lemma lem4395036 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4395037 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term271 A B s f g) = (term261 A B s f g).
Proof. exact (MK_COMB (@lem4395036 A) (@lem4395035 A B s f g)). Qed.
Lemma lem4395038 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term263 A B s f g) = (term262 A B s f g).
Proof. exact (MK_COMB (@lem4395033 A B s f g) (@lem4395037 A B s f g)). Qed.
Lemma lem4395039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4395040 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term272 A B s f g) = (term273 A B s f g).
Proof. exact (MK_COMB (@lem4395039) (@lem4395038 A B s f g)). Qed.
Lemma lem4395041 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term265 A B s f g x) = (term238 A B s f g x).
Proof. exact (eq_refl (term265 A B s f g x)). Qed.
Lemma lem4395042 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4395043 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term274 A B s f g x) = (term275 A B s f g x).
Proof. exact (MK_COMB (@lem4395042) (@lem4395041 A B s f g x)). Qed.
Lemma lem4395044 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term269 A B s f g x) = (term258 A B x s f g).
Proof. exact (eq_refl (term269 A B s f g x)). Qed.
Lemma lem4395045 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term276 A B s f g x) = (term277 A B x s f g).
Proof. exact (MK_COMB (@lem4395043 A B s f g x) (@lem4395044 A B x s f g)). Qed.
Lemma lem4395046 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term278 A B s f g) = (term279 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4395045 A B x s f g)). Qed.
Lemma lem4395047 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4395048 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term264 A B s f g) = (term280 A B s f g).
Proof. exact (MK_COMB (@lem4395047 A) (@lem4395046 A B s f g)). Qed.
Lemma lem4395049 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((term263 A B s f g) = (term264 A B s f g)) = ((term262 A B s f g) = (term280 A B s f g)).
Proof. exact (MK_COMB (@lem4395040 A B s f g) (@lem4395048 A B s f g)). Qed.
Lemma lem4395050 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term262 A B s f g) = (term280 A B s f g).
Proof. exact (EQ_MP (@lem4395049 A B s f g) (@lem4395027 A B s f g)). Qed.
Lemma lem4395051 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term211 A B s f g) = (term280 A B s f g).
Proof. exact (TRANS (@lem4395023 A B s f g) (@lem4395050 A B s f g)). Qed.
Lemma lem4395052 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term165 A B s f g) = (term280 A B s f g).
Proof. exact (TRANS (@lem4394914 A B s f g) (@lem4395051 A B s f g)). Qed.
Lemma lem4395053 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term96 A B s f g) = (term280 A B s f g).
Proof. exact (TRANS (@lem4394465 A B s f g) (@lem4395052 A B s f g)). Qed.
Lemma lem4395054 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term96 A B s f g) : term280 A B s f g.
Proof. exact (EQ_MP (@lem4395053 A B s f g) (@lem4394343 A B s f g h1)). Qed.
Lemma lem4395055 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term277 A B x s f g) : term277 A B x s f g.
Proof. exact (h1). Qed.
Lemma lem4395074 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term112 A B s f g x) = (term112 A B s f g x).
Proof. exact (eq_refl (term112 A B s f g x)). Qed.
Lemma lem4395075 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term146 A B s f g) = (term146 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4395074 A B s f g x)). Qed.
Lemma lem4395076 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4395077 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term147 A B s f g) = (term147 A B s f g).
Proof. exact (MK_COMB (@lem4395076 A) (@lem4395075 A B s f g)). Qed.
Lemma lem4395092 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term128 A B s g x) = (term128 A B s g x).
Proof. exact (eq_refl (term128 A B s g x)). Qed.
Lemma lem4395093 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term136 A B s g) = (term136 A B s g).
Proof. exact (fun_ext (fun x : A => @lem4395092 A B s g x)). Qed.
Lemma lem4395094 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4395095 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term137 A B s g) = (term137 A B s g).
Proof. exact (MK_COMB (@lem4395094 A) (@lem4395093 A B s g)). Qed.
Lemma lem4395096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4395097 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term153 A B s g) = (term153 A B s g).
Proof. exact (MK_COMB (@lem4395096) (@lem4395095 A B s g)). Qed.
Lemma lem4395098 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term154 A B s f g) = (term154 A B s f g).
Proof. exact (MK_COMB (@lem4395097 A B s g) (@lem4395077 A B s f g)). Qed.
Lemma lem4395141 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) (x : A) : (term256 A B f s g x) = (term256 A B f s g x).
Proof. exact (eq_refl (term256 A B f s g x)). Qed.
Lemma lem4395142 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term258 A B x s f g) = (term258 A B x s f g).
Proof. exact (MK_COMB (@lem4395141 A B f s g x) (@lem4395098 A B s f g)). Qed.
Lemma lem4395183 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term223 A B s f g x) = (term223 A B s f g x).
Proof. exact (eq_refl (term223 A B s f g x)). Qed.
Lemma lem4395198 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term113 A B s g x) = (term113 A B s g x).
Proof. exact (eq_refl (term113 A B s g x)). Qed.
Lemma lem4395199 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term170 A B s g) = (term170 A B s g).
Proof. exact (fun_ext (fun x : A => @lem4395198 A B s g x)). Qed.
Lemma lem4395200 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4395201 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term184 A B s g) = (term184 A B s g).
Proof. exact (MK_COMB (@lem4395200 A) (@lem4395199 A B s g)). Qed.
Lemma lem4395220 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term112 A B s f g x) = (term112 A B s f g x).
Proof. exact (eq_refl (term112 A B s f g x)). Qed.
Lemma lem4395221 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term146 A B s f g) = (term146 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4395220 A B s f g x)). Qed.
Lemma lem4395222 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4395223 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term147 A B s f g) = (term147 A B s f g).
Proof. exact (MK_COMB (@lem4395222 A) (@lem4395221 A B s f g)). Qed.
Lemma lem4395224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4395225 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term181 A B s f g) = (term181 A B s f g).
Proof. exact (MK_COMB (@lem4395224) (@lem4395223 A B s f g)). Qed.
Lemma lem4395226 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term185 A B f s g) = (term185 A B f s g).
Proof. exact (MK_COMB (@lem4395225 A B s f g) (@lem4395201 A B s g)). Qed.
Lemma lem4395227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4395228 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> B) : (term186 A B f s g) = (term186 A B f s g).
Proof. exact (MK_COMB (@lem4395227) (@lem4395226 A B f s g)). Qed.
Lemma lem4395229 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term238 A B s f g x) = (term238 A B s f g x).
Proof. exact (MK_COMB (@lem4395228 A B f s g) (@lem4395183 A B s f g x)). Qed.
Lemma lem4395230 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4395231 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term275 A B s f g x) = (term275 A B s f g x).
Proof. exact (MK_COMB (@lem4395230) (@lem4395229 A B s f g x)). Qed.
Lemma lem4395232 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) : (term277 A B x s f g) = (term277 A B x s f g).
Proof. exact (MK_COMB (@lem4395231 A B s f g x) (@lem4395142 A B x s f g)). Qed.
Lemma lem4395233 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term277 A B x s f g) : term277 A B x s f g.
Proof. exact (EQ_MP (@lem4395232 A B x s f g) (@lem4395055 A B x s f g h1)). Qed.
Lemma lem4395234 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term238 A B s f g x.
Proof. exact (h1). Qed.
Lemma lem4395235 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term258 A B x s f g.
Proof. exact (h1). Qed.
Lemma lem4395236 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term223 A B s f g x.
Proof. exact (proj2 (@lem4395234 A B s f g x h1)). Qed.
Lemma lem4395237 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term185 A B f s g.
Proof. exact (proj1 (@lem4395234 A B s f g x h1)). Qed.
Lemma lem4395238 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term184 A B s g.
Proof. exact (proj2 (@lem4395237 A B s f g x h1)). Qed.
Lemma lem4395239 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term147 A B s f g.
Proof. exact (proj1 (@lem4395237 A B s f g x h1)). Qed.
Lemma lem4395240 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (h1 : term124 A B s g x) : term124 A B s g x.
Proof. exact (h1). Qed.
Lemma lem4395241 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term102 A B s f g x) : term102 A B s f g x.
Proof. exact (h1). Qed.
Lemma lem4395246 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term154 A B s f g.
Proof. exact (proj2 (@lem4395235 A B x s f g h1)). Qed.
Lemma lem4395247 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term110 A B f s g x.
Proof. exact (proj1 (@lem4395235 A B x s f g h1)). Qed.
Lemma lem4395248 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term147 A B s f g.
Proof. exact (proj2 (@lem4395246 A B x s f g h1)). Qed.
Lemma lem4395249 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term137 A B s g.
Proof. exact (proj1 (@lem4395246 A B x s f g h1)). Qed.
Lemma lem4395250 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term102 A B s f g x) : term102 A B s f g x.
Proof. exact (h1). Qed.
Lemma lem4395251 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (h1 : term106 A B s g x) : term106 A B s g x.
Proof. exact (h1). Qed.
Lemma lem4395276 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term113 A B s g x) = (term113 A B s g x).
Proof. exact (eq_refl (term113 A B s g x)). Qed.
Lemma lem4395277 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term170 A B s g) = (term170 A B s g).
Proof. exact (fun_ext (fun x : A => @lem4395276 A B s g x)). Qed.
Lemma lem4395278 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4395280 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term184 A B s g) = (term184 A B s g).
Proof. exact (MK_COMB (@lem4395278 A) (@lem4395277 A B s g)). Qed.
Lemma lem4395281 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term184 A B s g.
Proof. exact (EQ_MP (@lem4395280 A B s g) (@lem4395238 A B s f g x h1)). Qed.
Lemma lem4395297 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term112 A B s f g x) = (term112 A B s f g x).
Proof. exact (eq_refl (term112 A B s f g x)). Qed.
Lemma lem4395298 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term146 A B s f g) = (term146 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4395297 A B s f g x)). Qed.
Lemma lem4395299 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4395301 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term147 A B s f g) = (term147 A B s f g).
Proof. exact (MK_COMB (@lem4395299 A) (@lem4395298 A B s f g)). Qed.
Lemma lem4395302 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term147 A B s f g.
Proof. exact (EQ_MP (@lem4395301 A B s f g) (@lem4395239 A B s f g x h1)). Qed.
Lemma lem4395344 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) : (term112 A B s f g x) = (term112 A B s f g x).
Proof. exact (eq_refl (term112 A B s f g x)). Qed.
Lemma lem4395345 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term146 A B s f g) = (term146 A B s f g).
Proof. exact (fun_ext (fun x : A => @lem4395344 A B s f g x)). Qed.
Lemma lem4395346 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4395348 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term147 A B s f g) = (term147 A B s f g).
Proof. exact (MK_COMB (@lem4395346 A) (@lem4395345 A B s f g)). Qed.
Lemma lem4395349 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term147 A B s f g.
Proof. exact (EQ_MP (@lem4395348 A B s f g) (@lem4395248 A B x s f g h1)). Qed.
Lemma lem4395365 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) : (term128 A B s g x) = (term128 A B s g x).
Proof. exact (eq_refl (term128 A B s g x)). Qed.
Lemma lem4395366 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term136 A B s g) = (term136 A B s g).
Proof. exact (fun_ext (fun x : A => @lem4395365 A B s g x)). Qed.
Lemma lem4395367 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4395369 {A B : Type'} (s : A -> Prop) (g : A -> B) : (term137 A B s g) = (term137 A B s g).
Proof. exact (MK_COMB (@lem4395367 A) (@lem4395366 A B s g)). Qed.
Lemma lem4395370 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term137 A B s g.
Proof. exact (EQ_MP (@lem4395369 A B s g) (@lem4395249 A B x s f g h1)). Qed.
Lemma lem4395395 {A B : Type'} (_50214 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term174 A B s g _50214.
Proof. exact (@lem4395281 A B s f g x h1 _50214). Qed.
Lemma lem4395396 {A B : Type'} (s : A -> Prop) (g : A -> B) (_50214 : A) : (term174 A B s g _50214) = (term113 A B s g _50214).
Proof. exact (eq_refl (term174 A B s g _50214)). Qed.
Lemma lem4395398 {A B : Type'} (_50215 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term171 A B s f g _50215.
Proof. exact (@lem4395302 A B s f g x h1 _50215). Qed.
Lemma lem4395399 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50215 : A) : (term171 A B s f g _50215) = (term112 A B s f g _50215).
Proof. exact (eq_refl (term171 A B s f g _50215)). Qed.
Lemma lem4395407 {A B : Type'} (_50218 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term171 A B s f g _50218.
Proof. exact (@lem4395349 A B x s f g h1 _50218). Qed.
Lemma lem4395408 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50218 : A) : (term171 A B s f g _50218) = (term112 A B s f g _50218).
Proof. exact (eq_refl (term171 A B s f g _50218)). Qed.
Lemma lem4395410 {A B : Type'} (_50219 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term281 A B s g _50219.
Proof. exact (@lem4395370 A B x s f g h1 _50219). Qed.
Lemma lem4395411 {A B : Type'} (s : A -> Prop) (g : A -> B) (_50219 : A) : (term281 A B s g _50219) = (term128 A B s g _50219).
Proof. exact (eq_refl (term281 A B s g _50219)). Qed.
Lemma lem4395427 {A B : Type'} (_50214 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term113 A B s g _50214.
Proof. exact (EQ_MP (@lem4395396 A B s g _50214) (@lem4395395 A B _50214 s f g x h1)). Qed.
Lemma lem4395431 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (h1 : term124 A B s g x) : term282 A B g x.
Proof. exact (proj2 (@lem4395240 A B s g x h1)). Qed.
Lemma lem4395437 {A B : Type'} (_50215 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term112 A B s f g _50215.
Proof. exact (EQ_MP (@lem4395399 A B s f g _50215) (@lem4395398 A B _50215 s f g x h1)). Qed.
Lemma lem4395447 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term102 A B s f g x) : term98 A B f g x.
Proof. exact (proj2 (@lem4395241 A B s f g x h1)). Qed.
Lemma lem4395459 {A B : Type'} (_50218 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term112 A B s f g _50218.
Proof. exact (EQ_MP (@lem4395408 A B s f g _50218) (@lem4395407 A B _50218 x s f g h1)). Qed.
Lemma lem4395463 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term102 A B s f g x) : term98 A B f g x.
Proof. exact (proj2 (@lem4395250 A B s f g x h1)). Qed.
Lemma lem4395469 {A B : Type'} (_50219 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term128 A B s g _50219.
Proof. exact (EQ_MP (@lem4395411 A B s g _50219) (@lem4395410 A B _50219 x s f g h1)). Qed.
Lemma lem4395479 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (h1 : term106 A B s g x) : term283 A B g x.
Proof. exact (proj2 (@lem4395251 A B s g x h1)). Qed.
Lemma lem4395516 {B : Type'} (x : B) (y : B) (z : B) : term284 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem4395522 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (h1 : term124 A B s g x) : term104 A x s.
Proof. exact (proj1 (@lem4395240 A B s g x h1)). Qed.
Lemma lem4395523 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (h1 : term124 A B s g x) : term285 A x s.
Proof. exact (fun h0 : @IN A x s => @lem4395522 A B s g x h1). Qed.
Lemma lem4395525 (p : Prop) : (term286 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4395526 {A : Type'} (x : A) (s : A -> Prop) : (term285 A x s) = (term104 A x s).
Proof. exact (@lem4395525 (@IN A x s)). Qed.
Lemma lem4395527 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (h1 : term124 A B s g x) : term104 A x s.
Proof. exact (EQ_MP (@lem4395526 A x s) (@lem4395523 A B s g x h1)). Qed.
Lemma lem4395533 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4395534 {A B : Type'} (g : A -> B) (_50214 : A) (s : A -> Prop) : (term113 A B s g _50214) = (term287 A B g _50214 s).
Proof. exact (@lem4395533 ((@ARB B) = (g _50214)) (@IN A _50214 s)). Qed.
Lemma lem4395542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4395543 {A B : Type'} (g : A -> B) (_50214 : A) (s : A -> Prop) : (term288 A B s g _50214) = (term289 A B g _50214 s).
Proof. exact (MK_COMB (@lem4395542) (@lem4395534 A B g _50214 s)). Qed.
Lemma lem4395551 {A B : Type'} (g : A -> B) (_50214 : A) (s : A -> Prop) : (term287 A B g _50214 s) = (term287 A B g _50214 s).
Proof. exact (eq_refl (term287 A B g _50214 s)). Qed.
Lemma lem4395552 {A B : Type'} (g : A -> B) (_50214 : A) (s : A -> Prop) : ((term113 A B s g _50214) = (term287 A B g _50214 s)) = ((term287 A B g _50214 s) = (term287 A B g _50214 s)).
Proof. exact (MK_COMB (@lem4395543 A B g _50214 s) (@lem4395551 A B g _50214 s)). Qed.
Lemma lem4395554 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4395555 (x : Prop) : (x = x) = True.
Proof. exact (@lem4395554 Prop x). Qed.
Lemma lem4395556 {A B : Type'} (g : A -> B) (_50214 : A) (s : A -> Prop) : ((term287 A B g _50214 s) = (term287 A B g _50214 s)) = True.
Proof. exact (@lem4395555 (term287 A B g _50214 s)). Qed.
Lemma lem4395557 {A B : Type'} (g : A -> B) (_50214 : A) (s : A -> Prop) : ((term113 A B s g _50214) = (term287 A B g _50214 s)) = True.
Proof. exact (TRANS (@lem4395552 A B g _50214 s) (@lem4395556 A B g _50214 s)). Qed.
Lemma lem4395558 {A B : Type'} (g : A -> B) (_50214 : A) (s : A -> Prop) : True = ((term113 A B s g _50214) = (term287 A B g _50214 s)).
Proof. exact (SYM (@lem4395557 A B g _50214 s)). Qed.
Lemma lem4395559 {A B : Type'} (g : A -> B) (_50214 : A) (s : A -> Prop) : (term113 A B s g _50214) = (term287 A B g _50214 s).
Proof. exact (EQ_MP (@lem4395558 A B g _50214 s) (@lem0)). Qed.
Lemma lem4395560 {A B : Type'} (_50214 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term287 A B g _50214 s.
Proof. exact (EQ_MP (@lem4395559 A B g _50214 s) (@lem4395427 A B _50214 s f g x h1)). Qed.
Lemma lem4395562 (b : Prop) (a : Prop) : (a \/ b) = (term290 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4395565 {A B : Type'} (s : A -> Prop) (g : A -> B) (_50214 : A) : (term287 A B g _50214 s) = (term291 A B s g _50214).
Proof. exact (@lem4395562 (@IN A _50214 s) ((@ARB B) = (g _50214))). Qed.
Lemma lem4395568 {A B : Type'} (_50214 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term291 A B s g _50214.
Proof. exact (EQ_MP (@lem4395565 A B s g _50214) (@lem4395560 A B _50214 s f g x h1)). Qed.
Lemma lem4395569 {A B : Type'} (_50214 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term291 A B s g _50214.
Proof. exact (@lem4395568 A B _50214 s f g x h1). Qed.
Lemma lem4395570 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term291 A B s g x.
Proof. exact (@lem4395569 A B x s f g x h1). Qed.
Lemma lem4395573 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term124 A B s g x) (h2 : term238 A B s f g x) : (@ARB B) = (g x).
Proof. exact (@lem4395570 A B s f g x h2 (@lem4395527 A B s g x h1)). Qed.
Lemma lem4395574 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term124 A B s g x) (h2 : term238 A B s f g x) : term292 A B g x.
Proof. exact (fun h0 : term283 A B g x => @lem4395573 A B s f g x h1 h2). Qed.
Lemma lem4395576 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4395577 {A B : Type'} (g : A -> B) (x : A) : (term292 A B g x) = ((@ARB B) = (g x)).
Proof. exact (@lem4395576 ((@ARB B) = (g x))). Qed.
Lemma lem4395578 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term124 A B s g x) (h2 : term238 A B s f g x) : (@ARB B) = (g x).
Proof. exact (EQ_MP (@lem4395577 A B g x) (@lem4395574 A B s f g x h1 h2)). Qed.
Lemma lem4395580 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4395581 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4395580 B x). Qed.
Lemma lem4395582 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (@lem4395581 B (@ARB B)). Qed.
Lemma lem4395583 {B : Type'} : term294 B.
Proof. exact (fun h0 : term295 B => @lem4395582 B). Qed.
Lemma lem4395585 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4395586 {B : Type'} : (term294 B) = ((@ARB B) = (@ARB B)).
Proof. exact (@lem4395585 ((@ARB B) = (@ARB B))). Qed.
Lemma lem4395587 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (EQ_MP (@lem4395586 B) (@lem4395583 B)). Qed.
Lemma lem4395605 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4395606 {B : Type'} (y : B) (x : B) (z : B) : (term296 B x y z) = (term297 B y x z).
Proof. exact (@lem4395605 (y = z) (term298 B x z)). Qed.
Lemma lem4395616 {B : Type'} (x : B) (y : B) : (term299 B x y) = (term299 B x y).
Proof. exact (eq_refl (term299 B x y)). Qed.
Lemma lem4395617 {B : Type'} (y : B) (x : B) (z : B) : (term284 B x y z) = (term300 B y x z).
Proof. exact (MK_COMB (@lem4395616 B x y) (@lem4395606 B y x z)). Qed.
Lemma lem4395621 (q : Prop) (p : Prop) (r : Prop) : (term301 p q r) = (term301 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4395622 {B : Type'} (y : B) (x : B) (z : B) : (term300 B y x z) = (term302 B y x z).
Proof. exact (@lem4395621 (y = z) (term298 B x y) (term298 B x z)). Qed.
Lemma lem4395644 {B : Type'} (y : B) (x : B) (z : B) : (term284 B x y z) = (term302 B y x z).
Proof. exact (TRANS (@lem4395617 B y x z) (@lem4395622 B y x z)). Qed.
Lemma lem4395645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4395646 {B : Type'} (y : B) (x : B) (z : B) : (term303 B x y z) = (term304 B y x z).
Proof. exact (MK_COMB (@lem4395645) (@lem4395644 B y x z)). Qed.
Lemma lem4395668 {B : Type'} (y : B) (x : B) (z : B) : (term302 B y x z) = (term302 B y x z).
Proof. exact (eq_refl (term302 B y x z)). Qed.
Lemma lem4395669 {B : Type'} (y : B) (x : B) (z : B) : ((term284 B x y z) = (term302 B y x z)) = ((term302 B y x z) = (term302 B y x z)).
Proof. exact (MK_COMB (@lem4395646 B y x z) (@lem4395668 B y x z)). Qed.
Lemma lem4395671 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4395672 (x : Prop) : (x = x) = True.
Proof. exact (@lem4395671 Prop x). Qed.
Lemma lem4395673 {B : Type'} (y : B) (x : B) (z : B) : ((term302 B y x z) = (term302 B y x z)) = True.
Proof. exact (@lem4395672 (term302 B y x z)). Qed.
Lemma lem4395674 {B : Type'} (y : B) (x : B) (z : B) : ((term284 B x y z) = (term302 B y x z)) = True.
Proof. exact (TRANS (@lem4395669 B y x z) (@lem4395673 B y x z)). Qed.
Lemma lem4395675 {B : Type'} (y : B) (x : B) (z : B) : True = ((term284 B x y z) = (term302 B y x z)).
Proof. exact (SYM (@lem4395674 B y x z)). Qed.
Lemma lem4395676 {B : Type'} (y : B) (x : B) (z : B) : (term284 B x y z) = (term302 B y x z).
Proof. exact (EQ_MP (@lem4395675 B y x z) (@lem0)). Qed.
Lemma lem4395677 {B : Type'} (y : B) (x : B) (z : B) : term302 B y x z.
Proof. exact (EQ_MP (@lem4395676 B y x z) (@lem4395516 B x y z)). Qed.
Lemma lem4395679 (b : Prop) (a : Prop) : (a \/ b) = (term290 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4395680 {B : Type'} (x : B) (y : B) (z : B) : (term302 B y x z) = (term305 B x y z).
Proof. exact (@lem4395679 (term306 B y x z) (y = z)). Qed.
Lemma lem4395682 (a : Prop) (b : Prop) : (term307 a b) = (term308 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4395683 {B : Type'} (y : B) (x : B) (z : B) : (term309 B y x z) = (term310 B y x z).
Proof. exact (@lem4395682 (term298 B x y) (term298 B x z)). Qed.
Lemma lem4395685 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4395686 {B : Type'} (x : B) (y : B) : (term311 B x y) = (x = y).
Proof. exact (@lem4395685 (x = y)). Qed.
Lemma lem4395687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4395688 {B : Type'} (x : B) (y : B) : (term312 B x y) = (term313 B x y).
Proof. exact (MK_COMB (@lem4395687) (@lem4395686 B x y)). Qed.
Lemma lem4395690 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4395691 {B : Type'} (x : B) (z : B) : (term311 B x z) = (x = z).
Proof. exact (@lem4395690 (x = z)). Qed.
Lemma lem4395692 {B : Type'} (y : B) (x : B) (z : B) : (term310 B y x z) = (term314 B y x z).
Proof. exact (MK_COMB (@lem4395688 B x y) (@lem4395691 B x z)). Qed.
Lemma lem4395693 {B : Type'} (y : B) (x : B) (z : B) : (term309 B y x z) = (term314 B y x z).
Proof. exact (TRANS (@lem4395683 B y x z) (@lem4395692 B y x z)). Qed.
Lemma lem4395694 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4395695 {B : Type'} (y : B) (x : B) (z : B) : (term315 B y x z) = (term316 B y x z).
Proof. exact (MK_COMB (@lem4395694) (@lem4395693 B y x z)). Qed.
Lemma lem4395696 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4395697 {B : Type'} (x : B) (y : B) (z : B) : (term305 B x y z) = (term317 B x y z).
Proof. exact (MK_COMB (@lem4395695 B y x z) (@lem4395696 B y z)). Qed.
Lemma lem4395698 {B : Type'} (x : B) (y : B) (z : B) : (term302 B y x z) = (term317 B x y z).
Proof. exact (TRANS (@lem4395680 B x y z) (@lem4395697 B x y z)). Qed.
Lemma lem4395700 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term124 A B s g x) (h2 : term238 A B s f g x) : term318 A B g x.
Proof. exact (conj (@lem4395578 A B s f g x h1 h2) (@lem4395587 B)). Qed.
Lemma lem4395702 {B : Type'} (x : B) (y : B) (z : B) : term317 B x y z.
Proof. exact (EQ_MP (@lem4395698 B x y z) (@lem4395677 B y x z)). Qed.
Lemma lem4395703 {B : Type'} (x : B) (y : B) (z : B) : term317 B x y z.
Proof. exact (@lem4395702 B x y z). Qed.
Lemma lem4395704 {A B : Type'} (g : A -> B) (x : A) : term319 A B g x.
Proof. exact (@lem4395703 B (@ARB B) (g x) (@ARB B)). Qed.
Lemma lem4395707 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term124 A B s g x) (h2 : term238 A B s f g x) : (g x) = (@ARB B).
Proof. exact (@lem4395704 A B g x (@lem4395700 A B s f g x h1 h2)). Qed.
Lemma lem4395708 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term124 A B s g x) (h2 : term238 A B s f g x) : term320 A B g x.
Proof. exact (fun h0 : term282 A B g x => @lem4395707 A B s f g x h1 h2). Qed.
Lemma lem4395710 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4395711 {A B : Type'} (g : A -> B) (x : A) : (term320 A B g x) = ((g x) = (@ARB B)).
Proof. exact (@lem4395710 ((g x) = (@ARB B))). Qed.
Lemma lem4395712 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term124 A B s g x) (h2 : term238 A B s f g x) : (g x) = (@ARB B).
Proof. exact (EQ_MP (@lem4395711 A B g x) (@lem4395708 A B s f g x h1 h2)). Qed.
Lemma lem4395715 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4395717 {A B : Type'} (g : A -> B) (x : A) : (term282 A B g x) = (term321 A B g x).
Proof. exact (@lem4395715 ((g x) = (@ARB B))). Qed.
Lemma lem4395720 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (h1 : term124 A B s g x) : term321 A B g x.
Proof. exact (EQ_MP (@lem4395717 A B g x) (@lem4395431 A B s g x h1)). Qed.
Lemma lem4395723 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term124 A B s g x) (h2 : term238 A B s f g x) : False.
Proof. exact (@lem4395720 A B s g x h1 (@lem4395712 A B s f g x h1 h2)). Qed.
Lemma lem4395724 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term124 A B s g x) (h2 : term238 A B s f g x) : term322.
Proof. exact (fun h0 : ~ False => @lem4395723 A B s f g x h1 h2). Qed.
Lemma lem4395726 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4395727 : term322 = False.
Proof. exact (@lem4395726 False). Qed.
Lemma lem4395728 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term124 A B s g x) (h2 : term238 A B s f g x) : False.
Proof. exact (EQ_MP (@lem4395727) (@lem4395724 A B s f g x h1 h2)). Qed.
Lemma lem4395771 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term102 A B s f g x) : @IN A x s.
Proof. exact (proj1 (@lem4395241 A B s f g x h1)). Qed.
Lemma lem4395772 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term102 A B s f g x) : term323 A x s.
Proof. exact (fun h0 : term104 A x s => @lem4395771 A B s f g x h1). Qed.
Lemma lem4395774 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4395775 {A : Type'} (x : A) (s : A -> Prop) : (term323 A x s) = (@IN A x s).
Proof. exact (@lem4395774 (@IN A x s)). Qed.
Lemma lem4395776 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term102 A B s f g x) : @IN A x s.
Proof. exact (EQ_MP (@lem4395775 A x s) (@lem4395772 A B s f g x h1)). Qed.
Lemma lem4395782 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4395783 {A B : Type'} (f : A -> B) (g : A -> B) (_50215 : A) (s : A -> Prop) : (term112 A B s f g _50215) = (term324 A B f g _50215 s).
Proof. exact (@lem4395782 ((f _50215) = (g _50215)) (term104 A _50215 s)). Qed.
Lemma lem4395791 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4395792 {A B : Type'} (f : A -> B) (g : A -> B) (_50215 : A) (s : A -> Prop) : (term325 A B s f g _50215) = (term326 A B f g _50215 s).
Proof. exact (MK_COMB (@lem4395791) (@lem4395783 A B f g _50215 s)). Qed.
Lemma lem4395800 {A B : Type'} (f : A -> B) (g : A -> B) (_50215 : A) (s : A -> Prop) : (term324 A B f g _50215 s) = (term324 A B f g _50215 s).
Proof. exact (eq_refl (term324 A B f g _50215 s)). Qed.
Lemma lem4395801 {A B : Type'} (f : A -> B) (g : A -> B) (_50215 : A) (s : A -> Prop) : ((term112 A B s f g _50215) = (term324 A B f g _50215 s)) = ((term324 A B f g _50215 s) = (term324 A B f g _50215 s)).
Proof. exact (MK_COMB (@lem4395792 A B f g _50215 s) (@lem4395800 A B f g _50215 s)). Qed.
Lemma lem4395803 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4395804 (x : Prop) : (x = x) = True.
Proof. exact (@lem4395803 Prop x). Qed.
Lemma lem4395805 {A B : Type'} (f : A -> B) (g : A -> B) (_50215 : A) (s : A -> Prop) : ((term324 A B f g _50215 s) = (term324 A B f g _50215 s)) = True.
Proof. exact (@lem4395804 (term324 A B f g _50215 s)). Qed.
Lemma lem4395806 {A B : Type'} (f : A -> B) (g : A -> B) (_50215 : A) (s : A -> Prop) : ((term112 A B s f g _50215) = (term324 A B f g _50215 s)) = True.
Proof. exact (TRANS (@lem4395801 A B f g _50215 s) (@lem4395805 A B f g _50215 s)). Qed.
Lemma lem4395807 {A B : Type'} (f : A -> B) (g : A -> B) (_50215 : A) (s : A -> Prop) : True = ((term112 A B s f g _50215) = (term324 A B f g _50215 s)).
Proof. exact (SYM (@lem4395806 A B f g _50215 s)). Qed.
Lemma lem4395808 {A B : Type'} (f : A -> B) (g : A -> B) (_50215 : A) (s : A -> Prop) : (term112 A B s f g _50215) = (term324 A B f g _50215 s).
Proof. exact (EQ_MP (@lem4395807 A B f g _50215 s) (@lem0)). Qed.
Lemma lem4395809 {A B : Type'} (_50215 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term324 A B f g _50215 s.
Proof. exact (EQ_MP (@lem4395808 A B f g _50215 s) (@lem4395437 A B _50215 s f g x h1)). Qed.
Lemma lem4395811 (b : Prop) (a : Prop) : (a \/ b) = (term290 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4395812 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50215 : A) : (term324 A B f g _50215 s) = (term327 A B s f g _50215).
Proof. exact (@lem4395811 (term104 A _50215 s) ((f _50215) = (g _50215))). Qed.
Lemma lem4395814 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4395815 {A : Type'} (_50215 : A) (s : A -> Prop) : (term97 A _50215 s) = (@IN A _50215 s).
Proof. exact (@lem4395814 (@IN A _50215 s)). Qed.
Lemma lem4395816 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4395817 {A : Type'} (_50215 : A) (s : A -> Prop) : (term328 A _50215 s) = (term329 A _50215 s).
Proof. exact (MK_COMB (@lem4395816) (@lem4395815 A _50215 s)). Qed.
Lemma lem4395818 {A B : Type'} (f : A -> B) (g : A -> B) (_50215 : A) : ((f _50215) = (g _50215)) = ((f _50215) = (g _50215)).
Proof. exact (eq_refl ((f _50215) = (g _50215))). Qed.
Lemma lem4395819 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50215 : A) : (term327 A B s f g _50215) = (term69 A B s f g _50215).
Proof. exact (MK_COMB (@lem4395817 A _50215 s) (@lem4395818 A B f g _50215)). Qed.
Lemma lem4395820 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50215 : A) : (term324 A B f g _50215 s) = (term69 A B s f g _50215).
Proof. exact (TRANS (@lem4395812 A B s f g _50215) (@lem4395819 A B s f g _50215)). Qed.
Lemma lem4395823 {A B : Type'} (_50215 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term69 A B s f g _50215.
Proof. exact (EQ_MP (@lem4395820 A B s f g _50215) (@lem4395809 A B _50215 s f g x h1)). Qed.
Lemma lem4395824 {A B : Type'} (_50215 : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term69 A B s f g _50215.
Proof. exact (@lem4395823 A B _50215 s f g x h1). Qed.
Lemma lem4395825 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : term69 A B s f g x.
Proof. exact (@lem4395824 A B x s f g x h1). Qed.
Lemma lem4395828 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) (h2 : term102 A B s f g x) : (f x) = (g x).
Proof. exact (@lem4395825 A B s f g x h1 (@lem4395776 A B s f g x h2)). Qed.
Lemma lem4395829 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) (h2 : term102 A B s f g x) : term330 A B f g x.
Proof. exact (fun h0 : term98 A B f g x => @lem4395828 A B s f g x h1 h2). Qed.
Lemma lem4395831 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4395832 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term330 A B f g x) = ((f x) = (g x)).
Proof. exact (@lem4395831 ((f x) = (g x))). Qed.
Lemma lem4395833 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) (h2 : term102 A B s f g x) : (f x) = (g x).
Proof. exact (EQ_MP (@lem4395832 A B f g x) (@lem4395829 A B s f g x h1 h2)). Qed.
Lemma lem4395836 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4395838 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term98 A B f g x) = (term331 A B f g x).
Proof. exact (@lem4395836 ((f x) = (g x))). Qed.
Lemma lem4395841 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term102 A B s f g x) : term331 A B f g x.
Proof. exact (EQ_MP (@lem4395838 A B f g x) (@lem4395447 A B s f g x h1)). Qed.
Lemma lem4395844 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) (h2 : term102 A B s f g x) : False.
Proof. exact (@lem4395841 A B s f g x h2 (@lem4395833 A B s f g x h1 h2)). Qed.
Lemma lem4395845 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) (h2 : term102 A B s f g x) : term322.
Proof. exact (fun h0 : ~ False => @lem4395844 A B s f g x h1 h2). Qed.
Lemma lem4395847 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4395848 : term322 = False.
Proof. exact (@lem4395847 False). Qed.
Lemma lem4395849 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) (h2 : term102 A B s f g x) : False.
Proof. exact (EQ_MP (@lem4395848) (@lem4395845 A B s f g x h1 h2)). Qed.
Lemma lem4395892 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term102 A B s f g x) : @IN A x s.
Proof. exact (proj1 (@lem4395250 A B s f g x h1)). Qed.
Lemma lem4395893 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term102 A B s f g x) : term323 A x s.
Proof. exact (fun h0 : term104 A x s => @lem4395892 A B s f g x h1). Qed.
Lemma lem4395895 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4395896 {A : Type'} (x : A) (s : A -> Prop) : (term323 A x s) = (@IN A x s).
Proof. exact (@lem4395895 (@IN A x s)). Qed.
Lemma lem4395897 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term102 A B s f g x) : @IN A x s.
Proof. exact (EQ_MP (@lem4395896 A x s) (@lem4395893 A B s f g x h1)). Qed.
Lemma lem4395903 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4395904 {A B : Type'} (f : A -> B) (g : A -> B) (_50218 : A) (s : A -> Prop) : (term112 A B s f g _50218) = (term324 A B f g _50218 s).
Proof. exact (@lem4395903 ((f _50218) = (g _50218)) (term104 A _50218 s)). Qed.
Lemma lem4395912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4395913 {A B : Type'} (f : A -> B) (g : A -> B) (_50218 : A) (s : A -> Prop) : (term325 A B s f g _50218) = (term326 A B f g _50218 s).
Proof. exact (MK_COMB (@lem4395912) (@lem4395904 A B f g _50218 s)). Qed.
Lemma lem4395921 {A B : Type'} (f : A -> B) (g : A -> B) (_50218 : A) (s : A -> Prop) : (term324 A B f g _50218 s) = (term324 A B f g _50218 s).
Proof. exact (eq_refl (term324 A B f g _50218 s)). Qed.
Lemma lem4395922 {A B : Type'} (f : A -> B) (g : A -> B) (_50218 : A) (s : A -> Prop) : ((term112 A B s f g _50218) = (term324 A B f g _50218 s)) = ((term324 A B f g _50218 s) = (term324 A B f g _50218 s)).
Proof. exact (MK_COMB (@lem4395913 A B f g _50218 s) (@lem4395921 A B f g _50218 s)). Qed.
Lemma lem4395924 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4395925 (x : Prop) : (x = x) = True.
Proof. exact (@lem4395924 Prop x). Qed.
Lemma lem4395926 {A B : Type'} (f : A -> B) (g : A -> B) (_50218 : A) (s : A -> Prop) : ((term324 A B f g _50218 s) = (term324 A B f g _50218 s)) = True.
Proof. exact (@lem4395925 (term324 A B f g _50218 s)). Qed.
Lemma lem4395927 {A B : Type'} (f : A -> B) (g : A -> B) (_50218 : A) (s : A -> Prop) : ((term112 A B s f g _50218) = (term324 A B f g _50218 s)) = True.
Proof. exact (TRANS (@lem4395922 A B f g _50218 s) (@lem4395926 A B f g _50218 s)). Qed.
Lemma lem4395928 {A B : Type'} (f : A -> B) (g : A -> B) (_50218 : A) (s : A -> Prop) : True = ((term112 A B s f g _50218) = (term324 A B f g _50218 s)).
Proof. exact (SYM (@lem4395927 A B f g _50218 s)). Qed.
Lemma lem4395929 {A B : Type'} (f : A -> B) (g : A -> B) (_50218 : A) (s : A -> Prop) : (term112 A B s f g _50218) = (term324 A B f g _50218 s).
Proof. exact (EQ_MP (@lem4395928 A B f g _50218 s) (@lem0)). Qed.
Lemma lem4395930 {A B : Type'} (_50218 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term324 A B f g _50218 s.
Proof. exact (EQ_MP (@lem4395929 A B f g _50218 s) (@lem4395459 A B _50218 x s f g h1)). Qed.
Lemma lem4395932 (b : Prop) (a : Prop) : (a \/ b) = (term290 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4395933 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50218 : A) : (term324 A B f g _50218 s) = (term327 A B s f g _50218).
Proof. exact (@lem4395932 (term104 A _50218 s) ((f _50218) = (g _50218))). Qed.
Lemma lem4395935 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4395936 {A : Type'} (_50218 : A) (s : A -> Prop) : (term97 A _50218 s) = (@IN A _50218 s).
Proof. exact (@lem4395935 (@IN A _50218 s)). Qed.
Lemma lem4395937 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4395938 {A : Type'} (_50218 : A) (s : A -> Prop) : (term328 A _50218 s) = (term329 A _50218 s).
Proof. exact (MK_COMB (@lem4395937) (@lem4395936 A _50218 s)). Qed.
Lemma lem4395939 {A B : Type'} (f : A -> B) (g : A -> B) (_50218 : A) : ((f _50218) = (g _50218)) = ((f _50218) = (g _50218)).
Proof. exact (eq_refl ((f _50218) = (g _50218))). Qed.
Lemma lem4395940 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50218 : A) : (term327 A B s f g _50218) = (term69 A B s f g _50218).
Proof. exact (MK_COMB (@lem4395938 A _50218 s) (@lem4395939 A B f g _50218)). Qed.
Lemma lem4395941 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (_50218 : A) : (term324 A B f g _50218 s) = (term69 A B s f g _50218).
Proof. exact (TRANS (@lem4395933 A B s f g _50218) (@lem4395940 A B s f g _50218)). Qed.
Lemma lem4395944 {A B : Type'} (_50218 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term69 A B s f g _50218.
Proof. exact (EQ_MP (@lem4395941 A B s f g _50218) (@lem4395930 A B _50218 x s f g h1)). Qed.
Lemma lem4395945 {A B : Type'} (_50218 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term69 A B s f g _50218.
Proof. exact (@lem4395944 A B _50218 x s f g h1). Qed.
Lemma lem4395946 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term69 A B s f g x.
Proof. exact (@lem4395945 A B x x s f g h1). Qed.
Lemma lem4395949 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term102 A B s f g x) (h2 : term258 A B x s f g) : (f x) = (g x).
Proof. exact (@lem4395946 A B x s f g h2 (@lem4395897 A B s f g x h1)). Qed.
Lemma lem4395950 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term102 A B s f g x) (h2 : term258 A B x s f g) : term330 A B f g x.
Proof. exact (fun h0 : term98 A B f g x => @lem4395949 A B x s f g h1 h2). Qed.
Lemma lem4395952 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4395953 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term330 A B f g x) = ((f x) = (g x)).
Proof. exact (@lem4395952 ((f x) = (g x))). Qed.
Lemma lem4395954 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term102 A B s f g x) (h2 : term258 A B x s f g) : (f x) = (g x).
Proof. exact (EQ_MP (@lem4395953 A B f g x) (@lem4395950 A B x s f g h1 h2)). Qed.
Lemma lem4395957 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4395959 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term98 A B f g x) = (term331 A B f g x).
Proof. exact (@lem4395957 ((f x) = (g x))). Qed.
Lemma lem4395962 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term102 A B s f g x) : term331 A B f g x.
Proof. exact (EQ_MP (@lem4395959 A B f g x) (@lem4395463 A B s f g x h1)). Qed.
Lemma lem4395965 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term102 A B s f g x) (h2 : term258 A B x s f g) : False.
Proof. exact (@lem4395962 A B s f g x h1 (@lem4395954 A B x s f g h1 h2)). Qed.
Lemma lem4395966 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term102 A B s f g x) (h2 : term258 A B x s f g) : term322.
Proof. exact (fun h0 : ~ False => @lem4395965 A B x s f g h1 h2). Qed.
Lemma lem4395968 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4395969 : term322 = False.
Proof. exact (@lem4395968 False). Qed.
Lemma lem4395970 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term102 A B s f g x) (h2 : term258 A B x s f g) : False.
Proof. exact (EQ_MP (@lem4395969) (@lem4395966 A B x s f g h1 h2)). Qed.
Lemma lem4396007 {B : Type'} (x : B) (y : B) (z : B) : term284 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem4396013 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (h1 : term106 A B s g x) : term104 A x s.
Proof. exact (proj1 (@lem4395251 A B s g x h1)). Qed.
Lemma lem4396014 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (h1 : term106 A B s g x) : term285 A x s.
Proof. exact (fun h0 : @IN A x s => @lem4396013 A B s g x h1). Qed.
Lemma lem4396016 (p : Prop) : (term286 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4396017 {A : Type'} (x : A) (s : A -> Prop) : (term285 A x s) = (term104 A x s).
Proof. exact (@lem4396016 (@IN A x s)). Qed.
Lemma lem4396018 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (h1 : term106 A B s g x) : term104 A x s.
Proof. exact (EQ_MP (@lem4396017 A x s) (@lem4396014 A B s g x h1)). Qed.
Lemma lem4396024 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4396025 {A B : Type'} (g : A -> B) (_50219 : A) (s : A -> Prop) : (term128 A B s g _50219) = (term332 A B g _50219 s).
Proof. exact (@lem4396024 ((g _50219) = (@ARB B)) (@IN A _50219 s)). Qed.
Lemma lem4396033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4396034 {A B : Type'} (g : A -> B) (_50219 : A) (s : A -> Prop) : (term333 A B s g _50219) = (term334 A B g _50219 s).
Proof. exact (MK_COMB (@lem4396033) (@lem4396025 A B g _50219 s)). Qed.
Lemma lem4396042 {A B : Type'} (g : A -> B) (_50219 : A) (s : A -> Prop) : (term332 A B g _50219 s) = (term332 A B g _50219 s).
Proof. exact (eq_refl (term332 A B g _50219 s)). Qed.
Lemma lem4396043 {A B : Type'} (g : A -> B) (_50219 : A) (s : A -> Prop) : ((term128 A B s g _50219) = (term332 A B g _50219 s)) = ((term332 A B g _50219 s) = (term332 A B g _50219 s)).
Proof. exact (MK_COMB (@lem4396034 A B g _50219 s) (@lem4396042 A B g _50219 s)). Qed.
Lemma lem4396045 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4396046 (x : Prop) : (x = x) = True.
Proof. exact (@lem4396045 Prop x). Qed.
Lemma lem4396047 {A B : Type'} (g : A -> B) (_50219 : A) (s : A -> Prop) : ((term332 A B g _50219 s) = (term332 A B g _50219 s)) = True.
Proof. exact (@lem4396046 (term332 A B g _50219 s)). Qed.
Lemma lem4396048 {A B : Type'} (g : A -> B) (_50219 : A) (s : A -> Prop) : ((term128 A B s g _50219) = (term332 A B g _50219 s)) = True.
Proof. exact (TRANS (@lem4396043 A B g _50219 s) (@lem4396047 A B g _50219 s)). Qed.
Lemma lem4396049 {A B : Type'} (g : A -> B) (_50219 : A) (s : A -> Prop) : True = ((term128 A B s g _50219) = (term332 A B g _50219 s)).
Proof. exact (SYM (@lem4396048 A B g _50219 s)). Qed.
Lemma lem4396050 {A B : Type'} (g : A -> B) (_50219 : A) (s : A -> Prop) : (term128 A B s g _50219) = (term332 A B g _50219 s).
Proof. exact (EQ_MP (@lem4396049 A B g _50219 s) (@lem0)). Qed.
Lemma lem4396051 {A B : Type'} (_50219 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term332 A B g _50219 s.
Proof. exact (EQ_MP (@lem4396050 A B g _50219 s) (@lem4395469 A B _50219 x s f g h1)). Qed.
Lemma lem4396053 (b : Prop) (a : Prop) : (a \/ b) = (term290 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4396056 {A B : Type'} (s : A -> Prop) (g : A -> B) (_50219 : A) : (term332 A B g _50219 s) = (term71 A B s g _50219).
Proof. exact (@lem4396053 (@IN A _50219 s) ((g _50219) = (@ARB B))). Qed.
Lemma lem4396059 {A B : Type'} (_50219 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term71 A B s g _50219.
Proof. exact (EQ_MP (@lem4396056 A B s g _50219) (@lem4396051 A B _50219 x s f g h1)). Qed.
Lemma lem4396060 {A B : Type'} (_50219 : A) (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term71 A B s g _50219.
Proof. exact (@lem4396059 A B _50219 x s f g h1). Qed.
Lemma lem4396061 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : term71 A B s g x.
Proof. exact (@lem4396060 A B x x s f g h1). Qed.
Lemma lem4396064 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term106 A B s g x) (h2 : term258 A B x s f g) : (g x) = (@ARB B).
Proof. exact (@lem4396061 A B x s f g h2 (@lem4396018 A B s g x h1)). Qed.
Lemma lem4396065 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term106 A B s g x) (h2 : term258 A B x s f g) : term320 A B g x.
Proof. exact (fun h0 : term282 A B g x => @lem4396064 A B x s f g h1 h2). Qed.
Lemma lem4396067 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4396068 {A B : Type'} (g : A -> B) (x : A) : (term320 A B g x) = ((g x) = (@ARB B)).
Proof. exact (@lem4396067 ((g x) = (@ARB B))). Qed.
Lemma lem4396069 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term106 A B s g x) (h2 : term258 A B x s f g) : (g x) = (@ARB B).
Proof. exact (EQ_MP (@lem4396068 A B g x) (@lem4396065 A B x s f g h1 h2)). Qed.
Lemma lem4396071 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4396072 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4396071 B x). Qed.
Lemma lem4396073 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (@lem4396072 B (g x)). Qed.
Lemma lem4396074 {A B : Type'} (g : A -> B) (x : A) : term335 A B g x.
Proof. exact (fun h0 : term336 A B g x => @lem4396073 A B g x). Qed.
Lemma lem4396076 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4396077 {A B : Type'} (g : A -> B) (x : A) : (term335 A B g x) = ((g x) = (g x)).
Proof. exact (@lem4396076 ((g x) = (g x))). Qed.
Lemma lem4396078 {A B : Type'} (g : A -> B) (x : A) : (g x) = (g x).
Proof. exact (EQ_MP (@lem4396077 A B g x) (@lem4396074 A B g x)). Qed.
Lemma lem4396096 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4396097 {B : Type'} (y : B) (x : B) (z : B) : (term296 B x y z) = (term297 B y x z).
Proof. exact (@lem4396096 (y = z) (term298 B x z)). Qed.
Lemma lem4396107 {B : Type'} (x : B) (y : B) : (term299 B x y) = (term299 B x y).
Proof. exact (eq_refl (term299 B x y)). Qed.
Lemma lem4396108 {B : Type'} (y : B) (x : B) (z : B) : (term284 B x y z) = (term300 B y x z).
Proof. exact (MK_COMB (@lem4396107 B x y) (@lem4396097 B y x z)). Qed.
Lemma lem4396112 (q : Prop) (p : Prop) (r : Prop) : (term301 p q r) = (term301 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4396113 {B : Type'} (y : B) (x : B) (z : B) : (term300 B y x z) = (term302 B y x z).
Proof. exact (@lem4396112 (y = z) (term298 B x y) (term298 B x z)). Qed.
Lemma lem4396135 {B : Type'} (y : B) (x : B) (z : B) : (term284 B x y z) = (term302 B y x z).
Proof. exact (TRANS (@lem4396108 B y x z) (@lem4396113 B y x z)). Qed.
Lemma lem4396136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4396137 {B : Type'} (y : B) (x : B) (z : B) : (term303 B x y z) = (term304 B y x z).
Proof. exact (MK_COMB (@lem4396136) (@lem4396135 B y x z)). Qed.
Lemma lem4396159 {B : Type'} (y : B) (x : B) (z : B) : (term302 B y x z) = (term302 B y x z).
Proof. exact (eq_refl (term302 B y x z)). Qed.
Lemma lem4396160 {B : Type'} (y : B) (x : B) (z : B) : ((term284 B x y z) = (term302 B y x z)) = ((term302 B y x z) = (term302 B y x z)).
Proof. exact (MK_COMB (@lem4396137 B y x z) (@lem4396159 B y x z)). Qed.
Lemma lem4396162 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4396163 (x : Prop) : (x = x) = True.
Proof. exact (@lem4396162 Prop x). Qed.
Lemma lem4396164 {B : Type'} (y : B) (x : B) (z : B) : ((term302 B y x z) = (term302 B y x z)) = True.
Proof. exact (@lem4396163 (term302 B y x z)). Qed.
Lemma lem4396165 {B : Type'} (y : B) (x : B) (z : B) : ((term284 B x y z) = (term302 B y x z)) = True.
Proof. exact (TRANS (@lem4396160 B y x z) (@lem4396164 B y x z)). Qed.
Lemma lem4396166 {B : Type'} (y : B) (x : B) (z : B) : True = ((term284 B x y z) = (term302 B y x z)).
Proof. exact (SYM (@lem4396165 B y x z)). Qed.
Lemma lem4396167 {B : Type'} (y : B) (x : B) (z : B) : (term284 B x y z) = (term302 B y x z).
Proof. exact (EQ_MP (@lem4396166 B y x z) (@lem0)). Qed.
Lemma lem4396168 {B : Type'} (y : B) (x : B) (z : B) : term302 B y x z.
Proof. exact (EQ_MP (@lem4396167 B y x z) (@lem4396007 B x y z)). Qed.
Lemma lem4396170 (b : Prop) (a : Prop) : (a \/ b) = (term290 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4396171 {B : Type'} (x : B) (y : B) (z : B) : (term302 B y x z) = (term305 B x y z).
Proof. exact (@lem4396170 (term306 B y x z) (y = z)). Qed.
Lemma lem4396173 (a : Prop) (b : Prop) : (term307 a b) = (term308 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4396174 {B : Type'} (y : B) (x : B) (z : B) : (term309 B y x z) = (term310 B y x z).
Proof. exact (@lem4396173 (term298 B x y) (term298 B x z)). Qed.
Lemma lem4396176 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4396177 {B : Type'} (x : B) (y : B) : (term311 B x y) = (x = y).
Proof. exact (@lem4396176 (x = y)). Qed.
Lemma lem4396178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4396179 {B : Type'} (x : B) (y : B) : (term312 B x y) = (term313 B x y).
Proof. exact (MK_COMB (@lem4396178) (@lem4396177 B x y)). Qed.
Lemma lem4396181 (a : Prop) : (term68 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4396182 {B : Type'} (x : B) (z : B) : (term311 B x z) = (x = z).
Proof. exact (@lem4396181 (x = z)). Qed.
Lemma lem4396183 {B : Type'} (y : B) (x : B) (z : B) : (term310 B y x z) = (term314 B y x z).
Proof. exact (MK_COMB (@lem4396179 B x y) (@lem4396182 B x z)). Qed.
Lemma lem4396184 {B : Type'} (y : B) (x : B) (z : B) : (term309 B y x z) = (term314 B y x z).
Proof. exact (TRANS (@lem4396174 B y x z) (@lem4396183 B y x z)). Qed.
Lemma lem4396185 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4396186 {B : Type'} (y : B) (x : B) (z : B) : (term315 B y x z) = (term316 B y x z).
Proof. exact (MK_COMB (@lem4396185) (@lem4396184 B y x z)). Qed.
Lemma lem4396187 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4396188 {B : Type'} (x : B) (y : B) (z : B) : (term305 B x y z) = (term317 B x y z).
Proof. exact (MK_COMB (@lem4396186 B y x z) (@lem4396187 B y z)). Qed.
Lemma lem4396189 {B : Type'} (x : B) (y : B) (z : B) : (term302 B y x z) = (term317 B x y z).
Proof. exact (TRANS (@lem4396171 B x y z) (@lem4396188 B x y z)). Qed.
Lemma lem4396191 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term106 A B s g x) (h2 : term258 A B x s f g) : term337 A B g x.
Proof. exact (conj (@lem4396069 A B x s f g h1 h2) (@lem4396078 A B g x)). Qed.
Lemma lem4396193 {B : Type'} (x : B) (y : B) (z : B) : term317 B x y z.
Proof. exact (EQ_MP (@lem4396189 B x y z) (@lem4396168 B y x z)). Qed.
Lemma lem4396194 {B : Type'} (x : B) (y : B) (z : B) : term317 B x y z.
Proof. exact (@lem4396193 B x y z). Qed.
Lemma lem4396195 {A B : Type'} (g : A -> B) (x : A) : term338 A B g x.
Proof. exact (@lem4396194 B (g x) (@ARB B) (g x)). Qed.
Lemma lem4396198 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term106 A B s g x) (h2 : term258 A B x s f g) : (@ARB B) = (g x).
Proof. exact (@lem4396195 A B g x (@lem4396191 A B x s f g h1 h2)). Qed.
Lemma lem4396199 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term106 A B s g x) (h2 : term258 A B x s f g) : term292 A B g x.
Proof. exact (fun h0 : term283 A B g x => @lem4396198 A B x s f g h1 h2). Qed.
Lemma lem4396201 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4396202 {A B : Type'} (g : A -> B) (x : A) : (term292 A B g x) = ((@ARB B) = (g x)).
Proof. exact (@lem4396201 ((@ARB B) = (g x))). Qed.
Lemma lem4396203 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term106 A B s g x) (h2 : term258 A B x s f g) : (@ARB B) = (g x).
Proof. exact (EQ_MP (@lem4396202 A B g x) (@lem4396199 A B x s f g h1 h2)). Qed.
Lemma lem4396206 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4396208 {A B : Type'} (g : A -> B) (x : A) : (term283 A B g x) = (term339 A B g x).
Proof. exact (@lem4396206 ((@ARB B) = (g x))). Qed.
Lemma lem4396211 {A B : Type'} (s : A -> Prop) (g : A -> B) (x : A) (h1 : term106 A B s g x) : term339 A B g x.
Proof. exact (EQ_MP (@lem4396208 A B g x) (@lem4395479 A B s g x h1)). Qed.
Lemma lem4396214 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term106 A B s g x) (h2 : term258 A B x s f g) : False.
Proof. exact (@lem4396211 A B s g x h1 (@lem4396203 A B x s f g h1 h2)). Qed.
Lemma lem4396215 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term106 A B s g x) (h2 : term258 A B x s f g) : term322.
Proof. exact (fun h0 : ~ False => @lem4396214 A B x s f g h1 h2). Qed.
Lemma lem4396217 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4396218 : term322 = False.
Proof. exact (@lem4396217 False). Qed.
Lemma lem4396219 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term106 A B s g x) (h2 : term258 A B x s f g) : False.
Proof. exact (EQ_MP (@lem4396218) (@lem4396215 A B x s f g h1 h2)). Qed.
Lemma lem4396220 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term258 A B x s f g) : False.
Proof. exact (or_elim (@lem4395247 A B x s f g h1) (fun h0 : term102 A B s f g x => @lem4395970 A B x s f g h0 h1) (fun h0 : term106 A B s g x => @lem4396219 A B x s f g h0 h1)). Qed.
Lemma lem4396221 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (x : A) (h1 : term238 A B s f g x) : False.
Proof. exact (or_elim (@lem4395236 A B s f g x h1) (fun h0 : term124 A B s g x => @lem4395728 A B s f g x h0 h1) (fun h0 : term102 A B s f g x => @lem4395849 A B s f g x h1 h0)). Qed.
Lemma lem4396222 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term277 A B x s f g) : False.
Proof. exact (or_elim (@lem4395233 A B x s f g h1) (fun h0 : term238 A B s f g x => @lem4396221 A B s f g x h0) (fun h0 : term258 A B x s f g => @lem4396220 A B x s f g h0)). Qed.
Lemma lem4396223 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term277 A B x s f g) : (term277 A B x s f g) = False.
Proof. exact (prop_ext (fun h2 : term277 A B x s f g => @lem4396222 A B x s f g h1) (fun h2 : False => @lem4395233 A B x s f g h1)). Qed.
Lemma lem4396224 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term277 A B x s f g) : False.
Proof. exact (EQ_MP (@lem4396223 A B x s f g h1) (@lem4395233 A B x s f g h1)). Qed.
Lemma lem4396225 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term96 A B s f g) : False.
Proof. exact (ex_elim (@lem4395054 A B s f g h1) (fun x : A => fun h0 : term279 A B s f g x => @lem4396224 A B x s f g h0)). Qed.
Lemma lem4396226 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term96 A B s f g) : (term96 A B s f g) = False.
Proof. exact (prop_ext (fun h2 : term96 A B s f g => @lem4396225 A B s f g h1) (fun h2 : False => @lem4394343 A B s f g h1)). Qed.
Lemma lem4396227 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) (h1 : term96 A B s f g) : False.
Proof. exact (EQ_MP (@lem4396226 A B s f g h1) (@lem4394343 A B s f g h1)). Qed.
Lemma lem4396228 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term95 A B s f g.
Proof. exact (fun h0 : term96 A B s f g => @lem4396227 A B s f g h0). Qed.
Lemma lem4396229 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term87 A B f s g) = (term48 A B s f g).
Proof. exact (EQ_MP (@lem4394342 A B s f g) (@lem4396228 A B s f g)). Qed.
Lemma lem4396234 {A B : Type'} (s : A -> Prop) (f : A -> B) : term90 A B s f.
Proof. exact (fun g : A -> B => @lem4396229 A B s f g). Qed.
Lemma lem4396239 {A B : Type'} (s : A -> Prop) : term92 A B s.
Proof. exact (fun f : A -> B => @lem4396234 A B s f). Qed.
Lemma lem4396244 {A B : Type'} : term94 A B.
Proof. exact (fun s : A -> Prop => @lem4396239 A B s). Qed.
Lemma lem4396245 {A B : Type'} : term62 A B.
Proof. exact (EQ_MP (@lem4394338 A B) (@lem4396244 A B)). Qed.
Lemma lem4396247 {A B : Type'} : term62 A B.
Proof. exact (@lem4394130 A B (@lem4396245 A B)). Qed.
Lemma lem4396248 {A B : Type'} (h1 : term63 A B) : False.
Proof. exact (@lem4396247 A B (@lem4394114 A B h1)). Qed.
Lemma lem4396249 {A B : Type'} (h1 : term63 A B) : (term63 A B) = False.
Proof. exact (prop_ext (fun h2 : term63 A B => @lem4396248 A B h1) (fun h2 : False => @lem4394114 A B h1)). Qed.
Lemma lem4396250 {A B : Type'} (h1 : term63 A B) : False.
Proof. exact (EQ_MP (@lem4396249 A B h1) (@lem4394114 A B h1)). Qed.
Lemma lem4396251 {A B : Type'} : term62 A B.
Proof. exact (fun h0 : term63 A B => @lem4396250 A B h0). Qed.
Lemma lem4396252 {A B : Type'} : term60 A B.
Proof. exact (EQ_MP (@lem4394113 A B) (@lem4396251 A B)). Qed.
Lemma lem4396253 {A B : Type'} : term59 A B.
Proof. exact (EQ_MP (@lem4394109 A B) (@lem4396252 A B)). Qed.

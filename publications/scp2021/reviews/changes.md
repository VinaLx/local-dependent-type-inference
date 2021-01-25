# Review 1

## Analysis & Related Work

> Clearer explanation of how lAI relates to other work.
> It would be a service to the field -- and to your readers -- to draw up a
> feature table comparing the features lAI shares (and does not share) with a
> variety of systems. In particular...

TODO

> The related work section omits two significant areas of inquiry:
> refinement type systems like F* and Liquid Haskell, and Amin's DOT theory...

TODO? But I know almost nothing about it.

> Clearer indication up front that implicits are necessarily proof irrelevant,
> and some concrete examples of programs your regime _disallows_.

TODO

> A stronger conclusion. Rather than just summarizing the ideas and
> listing future work, can you give a broader outlook? Supposing you
> had an algorithmic system... what would you be able to do now?

TODO

> Are there well formed types that are uninhabited? The monotype
> restriction on fixpoints may mean that diverging inhabitants can't
> be found at every type. The question of empty types seems
> important---on several occasions, the definitions and metatheory
> are forced to change because we don't know how to find inhabitants
> for arbitrary types. If there _were_ empty types, these
> metatheoretical concerns would be well justified. But if all types
> are inhabited, perhaps the theory can be made a touch simpler!

TODO: In the discussion, discuss the issue with strengthening.

## Proof Irrelevance

> p13L27 Why doesn't an implicit lambda just erase to its body? I was so
> confused I went and checked the Coq code, thinking the paper had a
> typo. It doesn't---I must have an 'understand-o'. But... what am I
> missing? There's some invariant or idea in the system that I haven't gotten.

TODO

> p14L50-57 I struggled with this paragraph. Can lAI handle vectors of
> implicit length, i.e., `Λn:Nat. λx:Vec n. ...`? A concrete example
> would really help here.

TODO

> p16L12-20 This paragraph is quite technical, but the gist of it should
> show up much earlier in the paper.

TODO

> p24L40 When you say "Implicit abstractions do not occur in type
> computation due to the kind restriction of universal types", it would
> be great to give an example of the kind of program that's
> forbidden... such an example would go a long way towards making it
> clear what your system can and can't handle!

TODO

> p24L56 I didn't understand this lemma. Shouldn't it be the case that
> `castdown N` has type `(\x:box. x) *`, and doesn't that type have kind
> `box`, and doesn't it reduce? What am I missing? (I'm sure it's me,
> and I just wonder what needs to be said to clear up my
> confusion. Sadly, stepping through the Coq proofs didn't help me.)

TODO: add little examples to illustrate the point (same for everything above)

## Syntax, naming, and notation

> p7L17 We haven't yet seen the grammar, so the reader isn't yet
> equipped to know what counts as a poly- or mono-type in your system
> (or that the distinction matters, depending on their familiarity with
> polymorphic subtyping and/or implicits!).

TODO

> p9L55 We still haven't seen the grammar... I had to flip forward at
> this point to be able to know which direction the definition was going
> in! Relatedly, the use of the word "binder" here to refer to the
> forall was somewhat confusing.

IGNORE

"Binder" should be a standard term to refer to the syntax construct to "bind"
a variable in the body. And the "binder" does not refer to `forall` type itself,
it refer to the inhabitants of `forall`.

> p10L15 It took quite some time to understand that mono-expressions
> exclude implicit foralls but not explicit pis... and allow _either_
> kind of lambda. I'm still a bit fuzzy on it, to be honest: a
> mono-expression can _have_ a type with implicits, but it can't _be_
> one? Right? More clarity here would be very helpful! Some kind of
> discussion should also go in "Implicit Polymorphism" on p11L24-38.

DONE?

Rephrase the paragraph of implicit polymorphism, which first emphasizes the idea
of generalization of polymorphic types
(and emphasize that the mono-types only excludes forall types not everything else).
Then mention the implicit lambda expression.

> p10L42 I'm not sure `Castup` and `Castdn` are the best possible names
> here. Why not just write $\mathsf{expand}$ and $\mathsf{reduce}$ for
> the terms (or `exp` and `red`)? These would be better rule names,
> too. The discussion here should perhaps cite Zombie.

IGNORE?

We follow the convention of the iso-type system here.

> p11L14 I'm not sure a 'mostly' adopted convention is worth
> mentioning. When _don't_ you do that?

IGNORE

For example the definition of transitivity we use e1, e2 and e3. Intuitively
transitivity should be a property concerning about subtyping, but our generalized
version talks about general terms as well. And it is not necessary in this circumstance
where e1 e2 and e3 mention terms or types.
So the convention is "mostly" adopted instead of "always",
we want to emphasize that while e1, e2 or A, B express identical meaning,
but there are subtle differences in different contexts.

> p12L20 If `Castdn` triggers only one step, why does the outer cast
> form remain in `R-Castdn`?

DONE

(no change)

Because castdn triggers type-level reduction,
which is performed in the typing rules, while in R-Castdn the castdn operator
only serves as an evaluation context.

> p14L20 Maybe call out the three non-structural rules (`S-Forall-L`,
> `S-Forall-R`, `S-Sub`)? The appearance of `S-Forall` to resolve some
> issues (p17L51) seems to indicate that "structurality" is an important
> property!

TODO?

> p14L36 Maybe highlight the new kinding premises?

TODO

> p16L21-25 I assumed the highlighted parts were important when I first
> read the figure, and I was surprised to see they were in fact
> redundant. I can imagine several useful highlights here: important
> kinding premises, premises added due to the issues in Section 4.1.1,
> places where mono-expressions are required, the three non-structural
> rules, and redundant premises. I'd put them in that order of
> importance. Maybe you can draw some `\fbox`en with various forms of
> dashing, or use colors, or something?

TODO

> p26L24-28 It'd be good to mark some turnstiles with a DK or
> something---it wasn't immediately obvious that the first turnstile was
> Dunfield and Krishnaswami's model of Oderskey and Läufer, and the
> second was your judgment.

DONE

Specify directly that we prove the subsumption of polymorphic subtyping, based
on the subsumption of DK's declarative subtyping. And add DK subscript to the
corresponding turnstiles.

> p26L30-43 I didn't understand these paragraphs at all.

TODO

> p28L37-38 "However, we still face..." didn't make any sense to me.

TODO

> It would be good to emphasize up front that pi and forall are
> different---the former explicitly takes an argument and the latter is
> implicit. I don't believe this is ever actually said in the paper!
> Calling out the difference between `S-Pi` and `S-Forall` would be a
> key move (p15).

DONE?

We add a sentence in section 3, "Implicit Polymorphism" to emphasize the
difference between \Lambda and \lambda expressions. As for the difference
between S-Pi and S-Forall, S-Pi is meant to be a generalization of the standard
subtyping rule of function type, and the motivation of S-Forall is explained in
section 4.1.

## Coq proofs

> It would be great to relate each theorem in the paper to its name in
> Coq and the file its proven in---I had to dig around a bit.

TODO

> p18L20-23 These lemmas have identical proof scripts. Why can't you
> prove it in one go? (You'd have to generalize your fancy tactic...)

TODO: but probably ignore

> p18L49 The substitution theorem here was quite surprising: only
> monotypes? Looking back at the rules, it's obvious: argument positions
> demand monotypes anyway, so this property is enough for the
> system. The text here, though, is confusing: its not _substitution_
> that "imposes a mono-expression restriction", but rather, the type
> system itself.

TODO: The assessment is not true

> p20L49 The proof of generalized transitivity seems to go by _strong_
> induction (i.e., due to the <= on the measures). Might be good to
> mention this in the paper.

TODO

> p21L11 Might be good to mention that Γ |- τ : A here.

TODO

> p21L34 At the comment about sizes of expressions I immediately
> wondered why you needed the derivation measure, too---and then saw it
> a minute later below. Maybe mention up front which cases call for
> which measures?

TODO

> p22L31-33 The Coq proofs of these progress theorems are more
> general. Maybe a short paragraph explaining the generality would be
> helpful?

TODO

> p23L39 I was surprised that the proof of subtype preservation is able
> to find the valid instantiation (necessarily constructively). I can't
> see the moment where that's happening in the custom tactics for the
> Coq proof, though. Some more intuition here would be nice.

TODO: but not quite understand what does it mean

## Other Comments

> p6L13 Maybe say earlier that `MkF` is constructing typeclass
> dictionaries? It's clear by the end of the page, but it will be easier
> for readers to know it up front. I would also explicitly mention that
> typeclass instantiation---a form of implicit argument in Haskell!---is
> out of scope here, due to proof irrelevance.

TODO

> p7L51 When you say "first attempt", it would be nice to give a clue as
> to what goes wrong... we find out later that the answer is
> 'metatheory'. Can you give a short indication that this is the case?
> Relatedly, are these rules admissible in the final system?

TODO

> p8L32 Can you explain how Hindley-Milner relates to the ICC rules
> (i.e., INST at variables and GEN at `let`s)?

TODO

> p17L18 You should indicate up front that this "possible
> generalization" is incorrect!

TODO

> p17L29 This premise `Γ,x:A |- B : *` just gives us what we would have
> tried to get by inversion... right?

TODO

> p17L43 The core issue here is that the type A may be bottom, i.e.,
> uninhabited... right?

TODO

> p29L54 GHC has type families, which certainly _feel_ like type-level
> lambdas. What do you mean here?

TODO


## Trivia

> Can you alphabetize your bibliography? The natbib package makes this easy.

TODO

> Some of the papers in the bibliography are miscapitalized, e.g.,
> "System fc" in [15].

TODO?

They are correct in the reference, so they are mis-auto-formated?

> Many citations are uneven: some just say POPL (e.g., [16]), while others
> say "ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages".
> I don't have a strong feeling about which is better, but I think consistency
> is nice here.

TODO

> Your Coq development works just fine on 8.12.0 (nice work, considering
> your heavy automation!), though your install instructions are missing
> the coq-ott package (and the omega tactic is deprecated in favor of
> lia---a mere warning).

IGNORE

> p2L35 "arizes" typo
> p8L46 "subsumption rule of [the] typing relation"
> p15 Figure 5 is too tall.
> p18L54 "take [the] following"
> p20L10 "head [a] Π type preserve[s] its kind"
> p22L13 "by employ designs to make" isn't quite grammatical
> p26L40 "to an open term" -> "on an open term"
> p26L44 "inside [a] cast operator"
> p26L50 "is a need" -> "would be a need"
> p27L16 "we do not really polymorphic kinds" missing word?
> p27L18 "then this complicates" -> "it would complicate"
> p27L50 "Such [a] restriction"
> p27L52 missing space before citation
> p28L16-19 run-on sentence
> p28L23 "Π type[s]"
> p28L36 "problem here stay at first-order" agreement; probably drop the hyphen
> p28L40 "We consider coming up with" where/when? do you mean it's future work?
> p29L9 "While since we" extra word?
> p29L18 missing space before citation
> p30L25 I'm not certain "hot topic" is the best choice of words here.
> p31L12 "eliminates [the] typing relation"

DONE.

"by employ designs to make" -> "by employing designs that make"
"hot topic in research" -> "research frontier"

# Recommendations

> Clarify up front that implicit arguments are proof
> irrelevant---perhaps even in the title! Given the various kinding
> and occurrence restrictions, what programs do you disallow?

TODO

> A feature table comparing related systems.

TODO: together with similar entry above

> A stronger conclusion, with more outlook for practice and/or
> application. What can we _do_ now (or when we have an algorithmic
> version of your system)?

TODO

> Consider proving whether or not all types are inhabited.

TODO: discuss it in the discussion

# Review 2

## Detail Comments

> For what I understand, the idea of unified subtyping has been the main novelty of reference [25], and also casts where already introduced there. Here the main novelty is the integration with polymorphism, however a more detailed comparison with [25] would be useful, also in technical aspects such as choices in the syntax, etc. Also, I had a look at [25] and some aspects (e.g, the role of casts in avoiding to have to compute type equality) are explained much bettere there, perhaps you could import some of these explanations.

TODO

> page 2 41-42 Here it is not clear which is the relation between strong normalization and explicit casts. Could you explain how explicit casts solve the problem? (see comment above, this is explained in [25])

TODO

> 17 at this point it is not clear what you mean by "conversion rule"

TODO

> page 5 the example of indexed lists is not completely clear. Is the n:N parameter the initial index of the list? if it is the case can you say this? because the role of indexes is never shown

TODO

> 29 I do not understand the role of the "r" parameter in the definition of List, can you explain?
> Please use a uniform font for code everywhere. For instance, map at line 34 is different from map at line 35.

TODO

> line 52: However, you do not show the definition of map

TODO: but probably ignore

> page 6: In the Functor example, it took me a lot of time to understand what is going on since you do not provide some simple explanation on Haskell-like syntax which I did not remember. It would be enough to recall that at line 13 Functor is defined by a record type, fmap is the name of the field selector, and field selection is written as application of the field selector.

TODO: but probably ignore

> It will also be useful to point out exactly what could not be expressed in, e.g., Haskell.
> You say (line 33) that F is implicitly instantiated, but F is not Functor Id here?

TODO

> page 7 you should explain which is the role of the type variables in Gamma; that is, what is only allowed if the type variable is available in Gamma

TODO

> page 10 line 50: should reference [42] be [41]? (that is, [25])

TODO

> Figure 2: you should at least mention the meaning of the "box" kind

TODO

> page 12: perhaps you should justify better why upcasts are values

TODO

> Figure 4: to use E both as metavariable and as index of the relation is a very bad choice (I was confused at the beginning)

TODO

> page 17 line 34 you use "fresh in A" to mean "not occurring in A", right?

TODO: probably ignore

> page 20 line 56 motivated by -> you mean "similar to"?

TODO

> page 24 line 18: which is the "inner" downcast?

TODO

> page 27 line 40: is it the first time that you mention principal type, perhaps should be defined

TODO

## Typos and minor comments

> page 2 31-32 repetition: ... a single level of syntax ... using the same syntax
> page 3 9 it results on -> it results in ?
> page 5 line 25 ommitted -> omitted
> page 6 line 38: and instead -> and, instead
> page 7 50 can be can be -> can be
> page 8
> 20 us -> our (?)
> polymorphism on dependent type language -> something is missing?
> page 11 line 10 similar syntax -> similar
> line 40: two full stops
> page 12 line 37 unfol -> unfold
> page 14 line 47 the -> these
> page 17 line 56 form -> from
> page 19 line 19 break -> breaks
> page 22 line 22 the sense -> in the sense
> page 23 line 30 a -> an
> 45 preserves the type of expression -> preserve the type of expressions
> page 26 line 22 terms type -> terms of type
> page 27 line 15 "we do not really" should be removed
> line 20 that, there -> that there
> line 57 the the -> the
> page 28 line 23 \Pi type -> \Pi types
> line 31 depedent -> dependent
> satisfy -> satisfies
> Rule rule -> rule
> stay -> stays
> Moreover -> Moreover,
> page 29 line 52 that, -> that
> page 30 line 28 work of -> work on
> enforce -> enforces
> page 31 line 42 of polymorphic -> on polymorphic

"... using the same syntax" -> rewrite to "i.e. the types are expressed ... using the same syntax as terms"
"in the subtyping rule (rule \forall L)" -> "in their subtyping rules (rule \forall L)"

DONE.

> callcc example: again, please use a different font for code

TODO

## References

> [1] American Matematical Society
> [25] and [41] are the same

DONE

> [14] Guru
> [15] System FC
> [20], [35], [55] Haskell

TODO?

They are correct in the reference, so they are mis-auto-formated?

# Review 3

## Analysis

>   The actual argument for the approach, though, wasn't great.  The indexed lists example seems super weird--it appears that indexes increase as the list goes on?  But I would expect the index to be the size of the list, and thus to decrease.  Consing onto a list won't work once you get to zero, which kind of defeats the purpose...or perhaps I'm not understanding something.
>
>   I also didn't understand the encoding technique in the list/map example.  What is r in the encoding of List?  Is this from Yang and Oliveira?
>
>   The functor example didn't do anything for me.  I expected this to mean functors in ML, but it wasn't.  I guess Haskell people will get it, but the example will be obscure for anyone not fully initiated into typed functional programming.

TODO?

> My biggest concern is the algorithmics of the system.  I understand this is a big challenge and the authors want to stage their work and leave that for another paper.  But to me it seems hopeless.  I know the Krishnaswami and Dunfield result was very difficult to obtain; at first glance this looks *much* harder.  And without automation, I can't see this system doing anyone any good; after all, the whole point of polymorphic subtyping is exactly so that type parameters can be automatically inferred.  So there's a gaping whole here--the approach is motivated mostly by practical concerns, but it isn't close to practical until the algorithmic issues are solved.  I do think the theory alone has some interest, though; so this is not a fatal flaw, but it is something that decreases my enthusiasm considerably.

TODO? Probably explain a little bit to the reviewer?


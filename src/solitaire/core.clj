(ns solitaire.core
  (:require clojure.edn
            [clojure.algo.monads :as m]
            [clojure.walk :refer [postwalk]]))

(defmethod print-method clojure.lang.PersistentQueue [q w] (print-method '<- w) (print-method (seq q) w) (print-method '-< w))

(def red #{:hearts :diamonds :d :h})

(defn red? [suit] (boolean (red suit)))

(defn black? [suit] (if suit (not (red? suit))))

(defn named [i]
  (if (nil? i)
    "empty space"
    (-> i name clojure.string/capitalize)))

(defn to-s [[rank suit]]
  (->> [(if (nil? rank) "an" "the") ({11 "Jack" 12 "Queen" 13 "King" 1 "Ace"} rank rank)
        (if-not (nil? rank) "of") ({:h "Hearts" :d "Diamonds" :s "Spades" :c "Clubs"} suit (named suit))]
       (remove nil?)
       (clojure.string/join " ")))

(defn card-range
  ([suit end] (card-range suit 1 end))
  ([suit] (card-range suit 13))
  ([suit begin end]
     (->> (range begin (inc end))
          (map #(vector % suit))
          vec)))

(defmacro ->cond [& args]
  (let [[body expr] (-> args count dec (split-at args))]
   `(cond-> ~@expr ~@body)))

(defn take-first [coll]
  (->> coll (drop-while nil?) (take 1)))

(defn peek-pop
  ([stack]
     [(peek stack) (if (seq stack) (pop stack))])
  ([stack n]
     (loop [x n
            result [[] stack]]
       (let [[_ stack] result]
         (if-let [next-item (and (> x 0) (peek stack))]
           (recur (dec x)
                  (-> result
                      (update-in [0] conj next-item)
                      (update-in [1] pop)))
           result)))))

(defn valid-card? [[rank suit :as card]]
            (and (seq card) (= (count card) 2)
                 rank (number? rank) (<= rank 13) (> rank 0)
                 (or (red? suit) (#{:c :s :clubs :spades} suit))))

(defn card [[rank suit]]
  [rank (keyword suit)])

(defn normalize [{:keys [stock foundation tableau]}]
  "Internal representation:
     :f Foundation: up to four sequences of cards
     :tableau a sequence of maps: {:h index of next hidden :s stack}
     :w Waste: a stack of cards
     :s Stock: a queue of cards
   Extra:
     :h Hidden Tableau: a sequence of up to seven (possibly nil) sequences of cards (possibly nil). Can
          be queried for cards, and remembered so that the user doens't need to repeatedly input the same
          card(s). The parameterized value in the state describes how the down-stacks are initalized."
  (letfn [(pad [n item coll]
            (->> (repeat item) (concat coll) (take n) vec))
          (cards [coll]
            (->> coll (partition 2) (map card)))]
    {:foundation (->> foundation (partition 2) (map (fn [[rank suit]] (card-range suit rank))) (pad 4 []))
     :tableau (->> tableau
                   (partition 2)
                   (map cards)
                   (map-indexed
                    (fn [index col]
                      {:stack (vec col) :hidden index}))
                   (pad 7 {:stack [] :hidden 0}))
     :waste []
     :stock (->> stock cards (into clojure.lang.PersistentQueue/EMPTY))}))

(defn parent-pred [[rank suit]]
  (fn [{parent-stack :stack}]
    (let [[parent-rank parent-suit] (peek parent-stack)]
      (and (= (red? parent-suit) (black? suit))
           (= parent-rank (inc rank))))))

(defn- get-history [state]
  (-> state meta :history reverse))

(defn- foundation-only? [[[[rank suit] {:keys [foundation]}] :as args]]
  (or (<= rank 2)
      (->> foundation
           (filter #(= (red? suit) (black? (-> % peek second))))
           (#(concat % (repeat nil)))
           (take 2)
           (every? #(let [[opposite-rank _] (peek %)]
                      ((fnil >= 1) opposite-rank (dec rank)))))))

(def ^:dynamic current-state)

(defn update-fn [fn-name new-state area index source-move-desc]
  (fn [form]
    (if (and (seq? form) (= (first form) fn-name))
      (let [[func & args] (second form)
            [_ _ & desc] form]
        `(-> ~new-state
             (~func ~(into [area index] (if (= :tableau area) [:stack])) ~@args)
             (vary-meta update-in [:history] conj
                        (clojure.string/join " " (list ~source-move-desc ~@desc)))))
      form)))

(defn process-args [func args]
  (if-not func
    args
    (let [result (func args)]
      (cond
       (seq? result) result
       (true? result) args))))

(defmacro destination [[map-fn-name area moved update-fn-name & {:keys [pre post]}] & body]
  (let [[state new-state desc] (repeatedly gensym)
        post-processing (if (symbol? post) [post] post)
        map-fn (fn [form]
                 (if (and (seq? form) (= (first form) map-fn-name))
                   (let [[index item] (second form)]
                     (postwalk (update-fn update-fn-name new-state area index desc)
                               `(->> ~state
                                     ~area
                                     (map-indexed
                                      (fn ~@(rest form)))
                                     ~@post-processing)))
                   form))]
    `(fn [& args#]
       (if-let [[& [[~moved ~new-state ~desc] ~state]] (process-args ~pre args#)]
         ~@(postwalk map-fn body)))))

(defmacro def-dest [name args & body]
  `(def ~name (destination ~args ~@body)))

(def-dest to-tableau 
  [foreach :tableau card accept :pre (complement foundation-only?)]
  (let [parent? (parent-pred card)]
    (foreach [index column]
             (if (parent? column)
               (accept (update-in conj card) "to tableau column" (inc index))))))

(defmacro foundation-dest [& pre-and-post-conditions]
  (list `destination
    (into '[foreach :foundation [rank suit :as card] accept] pre-and-post-conditions)
    '(let [ace? (= rank 1)
          [parent-rank? parent-suit?] (if ace? (repeat nil?)
                                          [#(= (dec rank) %) #(= suit %)])
          parent? (fn [[rank suit]] (and (parent-rank? rank) (parent-suit? suit)))]
      (foreach [index stack]
               (if (parent? (peek stack))
                  (accept (update-in conj card) "to foundation column" (inc index)))))))

(def to-foundation (foundation-dest :post take-first))
(def safe-foundation (foundation-dest :pre foundation-only? :post take-first))

(defn- use-single-card-stack? [[[[card :as stack] :as first-arg] state :as args]]
  (if (or (> (count stack) 1)
          (-> (rest first-arg)
              (conj card)
              (list state)
              ((complement foundation-only?))))
    args))

(def-dest orphan-parent
  [foreach :tableau [top-card :as stack] accept :pre use-single-card-stack?]
  (let [parent? (parent-pred top-card)]
    (foreach [index column]
             (if (parent? column)
               (accept (update-in into stack) "to" (-> column :stack last to-s) "at column" (inc index))))))

(def-dest empty-tableau
  [foreach :tableau king-stack accept :post take-first]
  (foreach [index {:keys [stack hidden]}]
    (if (and (= hidden 0) (empty? stack))
      (accept (assoc-in king-stack) "to column" (inc index)))))

(defn tableau-card [{:keys [tableau] :as state}]
  (->> tableau
       (map-indexed
        (fn [index {:keys [stack]}]
          (if (seq stack)
            [(peek stack) (update-in state [:tableau index :stack] pop)
             (str "Moved " (-> stack peek to-s) " from tableau column " (inc index))])))))

(defn waste-card [state]
  (letfn [(desc [card]
            (clojure.string/join " " ["Moved" (to-s card) "from waste pile"]))
          (create-source [card state return-values]
            (conj return-values [card (update-in state [:waste] pop) (desc card)]))
          (next-state [{:keys [stock waste] :as state}]
            (let [[new-waste new-stock] (peek-pop stock 3)]
              (if (empty? new-waste)
                (-> state
                    (update-in [:stock] into waste)
                    (update-in [:waste] empty))
                (-> state
                    (update-in [:waste] into new-waste)
                    (assoc :stock new-stock)))))]
    (loop [{:keys [waste stock] :as state} state
           return []]
     (if-let [card (peek waste)]
       (if (->> (map first return) (not-any? #(= % card)))
         (recur (next-state state) (create-source card state return))
         return)
       (if (or (seq stock) (seq waste))
         (recur (next-state state) return))))))

(defn move-type [& defns]
  (fn [state]
    (m/domonad (m/maybe-t m/sequence-m)
               [[find-movable destinations] (partition 2 defns)
                source (find-movable state)
                move (destinations source state)]
               move)))

(letfn [(orphan [{:keys [tableau] :as state}]
          (->> tableau
               (map-indexed
                (fn [index {[[rank] :as stack] :stack}]
                  (if (and rank (not= rank 13))
                    [stack (assoc-in state [:tableau index :stack] [])
                     (str "Moved orphan stack starting with " (to-s (peek stack)) " from column " (inc index))])))))
        (obscuring-king [{:keys [tableau] :as state}]
          (->> tableau
               (map-indexed
                (fn [index {[[rank] :as stack] :stack hidden :hidden}]
                  (if (and (= rank 13) (> hidden 0))
                    [stack (assoc-in state [:tableau index :stack] [])
                     (str "Moved " (-> stack peek to-s) "'s stack from column " (inc index))])))))
        (foundation-card [{:keys [foundation] :as state}]
          (->> foundation
               (map-indexed
                (fn [index column]
                  (if (seq column)
                    [(peek column) (update-in state [:foundation index] pop)
                     (str "Moved " (-> column peek to-s) " from foundation column " (inc index))])))))
        (reveal-cards [known-hidden query-cards]
          (fn [state]
            (->> (:tableau state)
                 (map-indexed
                  (fn [column-index {:keys [stack hidden] :as column}]
                    (if (and (empty? stack)
                             (> hidden 0))
                      (let [card
                            (if-let [known-card (known-hidden column-index hidden)]
                              known-card
                              (binding [current-state state]
                                (query-cards column-index hidden)))]
                        (-> column
                            (update-in [:stack] conj card)
                            (update-in [:hidden] dec)))
                      column)))
                 vec
                 (assoc state :tableau))))
        (destinations [x y]
          (fn [& args]
            (-> (juxt x y) (apply args) flatten)))]
  (defn find-moves
    ([initial-state]
       (let [moves (move-type
                    orphan orphan-parent
                    obscuring-king empty-tableau
                    tableau-card to-foundation
                   ; foundation-card to-tableau
                    waste-card (destinations to-foundation to-tableau))]
         (->> (loop [state initial-state]
                (let [[new-state] ((move-type tableau-card safe-foundation) state)]
                  (if new-state
                    (recur new-state)
                    state)))
              moves
              (remove nil?))))
    ([known-hidden query-hidden state]
       (->> state find-moves (map (reveal-cards known-hidden query-hidden))))))

(defn- query-hidden [col index]
  (if-let [previous-moves (seq (get-history current-state))]
    (dorun (map println previous-moves)))
  (println "What is at column" (inc col) "card number" index "?")
  (flush)
  (let [input (atom nil)]
    (while (not (valid-card? @input))
      (reset! input (->> clojure.edn/read repeatedly (take 2) card)))
    (println "Card read:" @input)
    @input))

(defn known-hidden [desc]
  (let [take-n (fn [coll index]
                 (take index coll))
        per-column (fn [index column]
                     (-> (for [card-seq (partition 2 column)] (card card-seq))
                         (concat (repeat nil))
                         (take-n index)
                         reverse
                         vec))
        hidden-cards (->> (-> desc :hidden-cards (concat (repeat nil)) (take-n 6))
                          (concat [nil])
                          (map-indexed per-column)
                          vec)]
    (fn [col idx] ((hidden-cards col) (dec idx)))))

(defn solve
  [initial-state]
  (let [get-next-moves (partial find-moves (known-hidden initial-state) (memoize query-hidden))
        winning? (fn [state]
                   (if (every? #(= 13 (count %)) (state :foundation))
                     (get-history state)))
        depth (atom 0)
        previous-parents (atom clojure.lang.PersistentQueue/EMPTY)]
    (loop [moves (->> initial-state normalize (conj []))]
      (let [new-depth (-> moves peek get-history count)]
        (when (> new-depth @depth)
         (reset! depth new-depth)
         (println "New max depth:" new-depth)
         (when (> new-depth 100)
           (dorun (map println (-> moves peek get-history)))
           (throw (IllegalStateException.)))))
      (if-let [winning-moves (some winning? moves)]
        winning-moves
        (if (seq moves)
          (->> (peek moves)
               get-next-moves
               distinct
               (remove #(some #{%} (concat moves @previous-parents)))
               (#(let [parent (peek moves)]
                   (swap! previous-parents conj parent)
                   (while (< 50 (count @previous-parents))
                     (swap! previous-parents pop))
                   (into (pop moves) %)))
               recur))))))

(def test-state '{:stock [6 h 8 c 1 c 5 c 2 c 6 d 10 c 1 h 5 h 3 d 1 d 2 h 9 h 12 c 11 c 7 c 11 h 8 s 5 d 6 s 4 c 11 d 7 h 3 h]
                  :tableau [12 d 3 s 13 c 2 s 9 d 2 d 6 c]
                  :hidden-cards [[12 s] [7 s 4 d] [9 c 13 s 5 s] [4 s 8 h 9 s 13 h] [10 d 1 s 10 s 12 h 4 h] [8 d 7 d 10 h]]})

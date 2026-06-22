MACHINE IntegratedRestaurant

CONSTANTS         
    insze, rnsze, max_ingredients_sze, max_recipes_sze, max_tables_sze, no_name_i, no_name_r
    
SETS
    INGREDIENTNAME; RECIPENAME; RESPONSE = {yes, no}

PROPERTIES
    insze : NAT1 & card(INGREDIENTNAME) = insze & rnsze : NAT1 & card(RECIPENAME) = rnsze
    & max_ingredients_sze : NAT1 & max_recipes_sze : NAT1 & max_tables_sze : NAT1
    & no_name_i : INGREDIENTNAME
    & no_name_r : RECIPENAME

VARIABLES    
    ingredients, ingredientNames, recipes, recipeIngredients, recipeNames, inventory, menu, expectedMenu, tables, pendingOrders, completedOrders

INVARIANT  
    ingredients <: NAT
    & card(ingredients) <= max_ingredients_sze
    & ingredientNames : ingredients >-> INGREDIENTNAME
    & recipes <: NAT
    & card(recipes) <= max_recipes_sze
    & recipeIngredients : recipes --> (ingredients +-> NAT1)
    & recipeNames : recipes >-> RECIPENAME 
    & inventory : ingredients --> NAT
    & menu <: recipes
    & expectedMenu : menu --> NAT1
    & tables <: NAT
    & card(tables) <= max_tables_sze
    & pendingOrders : tables --> (menu +-> NAT1)
    & completedOrders : menu --> NAT
    & !ii.(
        ii: ingredients => 
        SIGMA(rr).( rr : menu |
            SIGMA(tt).(tt: tables | ({rr |-> 0} <+ pendingOrders(tt))(rr))
            *
            ({ii |-> 0} <+ recipeIngredients(rr))(ii)
        ) <= inventory(ii)
    )

INITIALISATION 
    ingredients, ingredientNames, recipes, recipeIngredients, recipeNames, inventory, menu, expectedMenu, tables, pendingOrders, completedOrders := {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}

OPERATIONS
    
//    1 - Preparação do menu 
    
    idx <-- addIngredient(name) =
    PRE name : INGREDIENTNAME & name /: ran(ingredientNames) & card(ingredients) < max_ingredients_sze
    THEN 
        ANY ii WHERE ii : NAT & ii /: ingredients
        THEN
            ingredients := ingredients \/ {ii} ||
            ingredientNames(ii) := name ||
            inventory(ii) := 0||
            idx := ii
        END
    END;
    
    deleteIngredient(ii) =
    PRE ii : ingredients & !rr.(rr : recipes => ii /: dom(recipeIngredients(rr))) & inventory(ii) = 0
    THEN ingredients := ingredients - {ii} ||
        ingredientNames := {ii} <<| ingredientNames ||
        inventory := {ii} <<| inventory
    END;
    
    renameIngredient(ii, name) =
    PRE ii : ingredients & name : INGREDIENTNAME & name /: ran(ingredientNames)
    THEN ingredientNames(ii) := name
    END;
    
    il <-- getIngredientList =
    ANY idxToIngredient WHERE
        idxToIngredient : perm(ingredients)
    THEN il :=
        %ii.(ii : 0..card(ingredients)-1 |
            idxToIngredient(ii+1)
      )
    END;
    
    in <-- getIngredientName(ii) =
    PRE ii : ingredients
    THEN in := ingredientNames(ii)
    END;
    
    
    idx <-- addRecipe(name) =
    PRE name : RECIPENAME & name /: ran(recipeNames) & card(recipes) < max_recipes_sze
    THEN 
        ANY rr WHERE rr : NAT & rr /: recipes
        THEN
            recipes := recipes \/ {rr} ||
            recipeIngredients := recipeIngredients \/ {rr |-> {}} ||
            recipeNames(rr) := name ||
            idx := rr
        END
    END;
    
    deleteRecipe(rr) =
    PRE rr : recipes & rr /: menu
    THEN recipes := recipes - {rr} ||
        recipeIngredients := {rr} <<| recipeIngredients||
        recipeNames := {rr} <<| recipeNames
    END;
    
    renameRecipe(rr, name) =
    PRE rr : recipes & name : RECIPENAME & name /: ran(recipeNames)
    THEN recipeNames(rr) := name
    END;
    
    rl <-- getRecipeList =
    ANY idxToRecipe WHERE
        idxToRecipe : perm(recipes)
    THEN rl :=
        %ii.(ii : 0..card(recipes)-1 |
            idxToRecipe(ii+1)
      )
    END;
    
    rn <-- getRecipeName(rr) =
    PRE rr : recipes
    THEN rn := recipeNames(rr)
    END;
   
    addIngredientToRecipe(ii, rr, am) =
    PRE ii : ingredients & rr : recipes & am : NAT1 & ii /: dom(recipeIngredients(rr)) & rr /: menu
    THEN recipeIngredients(rr) := recipeIngredients(rr) \/ {ii |-> am}
    END; 
    
    updateIngredientAmount(ii, rr, am) =
    PRE ii : ingredients & rr : recipes & am : NAT1 & ii : dom(recipeIngredients(rr)) & rr /: menu
    THEN recipeIngredients(rr)(ii) := am
    END; 
    
    removeIngredientOfRecipe(ii, rr) =
    PRE ii : ingredients & rr : recipes & ii : dom(recipeIngredients(rr)) & rr /: menu
    THEN recipeIngredients(rr) := {ii} <<| recipeIngredients(rr)
    END;
    
    ri <-- getRecipeIngredients(rr) =
    PRE rr: recipes
    THEN
        ANY idxToRecipeIngredient WHERE
            idxToRecipeIngredient : perm(dom(recipeIngredients(rr)))
        THEN ri :=
            %ii.(ii : 0..card(dom(recipeIngredients(rr)))-1 |
                idxToRecipeIngredient(ii+1)
          )
        END
    END;
    
    resp <-- preGetRecipeIngredientAmount(rr, ii) =
    PRE rr: recipes & ii : ingredients
    THEN 
        IF ii : dom(recipeIngredients(rr))
            THEN resp := yes
            ELSE resp := no
            END
    END;
    
    ia <-- getRecipeIngredientAmount(rr, ii) =
    PRE rr: recipes & ii : ingredients & ii : dom(recipeIngredients(rr))
    THEN ia := recipeIngredients(rr)(ii)
    END;

    addRecipeToMenu(rr, am) =
    PRE rr : recipes & rr /: menu & am : NAT1
    THEN menu := menu \/ {rr} ||
        expectedMenu(rr) := am ||
        completedOrders(rr) := 0
    END;
    
    uptadeMenuRecipeExpectation(rr, am) =
    PRE rr : menu & am : NAT1
    THEN expectedMenu(rr) := am
    END;
    
    removeRecipeFromMenu(rr) =
    PRE rr : menu & !t1.(t1: tables => rr /: dom(pendingOrders(t1))) & completedOrders(rr) = 0
    THEN menu := menu - {rr} ||
        expectedMenu := {rr} <<| expectedMenu ||
        completedOrders := {rr} <<| completedOrders
    END;
    
    ml <-- getMenuList =
    ANY idxToMenuRecipe WHERE
        idxToMenuRecipe : perm(menu)
    THEN ml :=
        %ii.(ii : 0..card(menu)-1 |
            idxToMenuRecipe(ii+1)
      )
    END;
    
    em <-- getExpectedMenu(rr) =
    PRE rr : menu
    THEN em := expectedMenu(rr)
    END;
    
    idx <-- addTable =
    PRE card(tables) < max_tables_sze
    THEN
        ANY tt WHERE tt : NAT & tt /: tables
        THEN
            tables := tables \/ {tt}||
            pendingOrders := pendingOrders \/ {tt |-> {}}||
            idx := tt
        END
    END;
    
    removeTable(tt) =
    PRE tt : tables & pendingOrders(tt) = {}
    THEN tables := tables - {tt} ||
        pendingOrders := {tt} <<| pendingOrders
    END;
    
    tl <-- getTableList =
    ANY idxToTable WHERE
        idxToTable : perm(tables)
    THEN tl :=
        %ii.(ii : 0..card(tables)-1 |
            idxToTable(ii+1)
      )
    END;
    
    si <-- getIngredientAmountToShop(ii) =
    PRE ii : ingredients
    THEN  si :=   
        max(
            {
                SIGMA(rr).(rr : menu |
                    expectedMenu(rr) *
                    ({ii |-> 0} <+ recipeIngredients(rr))(ii)
                ) - inventory(ii),
                0
            }
        )

    END;
    
//    2 - Inventário 
    
    addItemToInventory(ii, am) =
    PRE ii : ingredients & am : NAT1 & (inventory(ii) + am) : NAT1
    THEN inventory(ii) := inventory(ii) + am
    END;
    
    removeItemOfInventory(ii, am) =
    PRE ii : ingredients & am : NAT1
        & SIGMA(rr).( rr : menu |
            SIGMA(tt).(tt: tables | ({rr |-> 0} <+ pendingOrders(tt))(rr))
            *
            ({ii |-> 0} <+ recipeIngredients(rr))(ii)
        ) <= inventory(ii) - am
    THEN inventory(ii) := inventory(ii) - am
    END;
    
    am <-- getItemInventoryAmount(ii) =
    PRE ii : ingredients
    THEN am := inventory(ii)
    END;
    
    
//    3 - Serviço 

    makeOrder(tt, rr, am) =
    PRE tt : tables & rr : menu & am :NAT1 & ({rr |-> 0} <+ pendingOrders(tt))(rr) + am : NAT1
        & !ii.(
            ii: ingredients => 
            SIGMA(r1).( r1 : menu |
                (
                    SIGMA(t1).(t1: tables | ({r1 |-> 0} <+ (pendingOrders(t1)))(r1)) 
                    + 
                    ({r1 |-> 0} <+ {rr |-> am})(r1)
                )
                *
                ({ii |-> 0} <+ recipeIngredients(r1))(ii)
            ) <= inventory(ii)
            
        )
    THEN pendingOrders(tt)(rr) := ({rr |-> 0} <+ pendingOrders(tt))(rr) + am
    END;
  
    cancelOrder(tt, rr, am) =
    PRE tt : tables & rr : menu & am :NAT1 & ({rr |-> 0} <+ pendingOrders(tt))(rr) >= am
    THEN
        IF ({rr |-> 0} <+ pendingOrders(tt))(rr) = am
        THEN pendingOrders(tt) := {rr} <<| pendingOrders(tt)
        ELSE pendingOrders(tt)(rr) := pendingOrders(tt)(rr) - am 
        END
    END;
    
    pr <-- getTablePendingRecipes(tt) =
    PRE tt: tables
    THEN
        ANY idxToMenuRecipe WHERE
            idxToMenuRecipe : perm(dom(pendingOrders(tt)))
        THEN pr :=
            %ii.(ii : 0..card(dom(pendingOrders(tt)))-1 |
                idxToMenuRecipe(ii+1)
          )
        END    
    END;
    
    resp <-- preGetTablePendingRecipeAmount(tt, rr) =
    PRE tt: tables & rr : menu
    THEN
        IF rr : dom(pendingOrders(tt))
        THEN resp := yes
        ELSE resp := no
        END
    END;
    
    pr <-- getTablePendingRecipeAmount(tt, rr) =
    PRE tt: tables & rr : menu & rr : dom(pendingOrders(tt))
    THEN pr := pendingOrders(tt)(rr)
    END;
    
    completeOrder(tt, rr, am) =
    PRE tt : tables & rr : menu & am :NAT1 & pendingOrders(tt)(rr) >= am & (completedOrders(rr) + am) : NAT1
    THEN completedOrders(rr) := completedOrders(rr) + am ||
         inventory := %ii.(ii : ingredients & ii /: dom(recipeIngredients(rr)) | inventory(ii))
                    \/ %ii.(ii : ingredients & ii : dom(recipeIngredients(rr)) | inventory(ii) - (recipeIngredients(rr)(ii) * am))||
        IF ({rr |-> 0} <+ pendingOrders(tt))(rr) = am
        THEN pendingOrders(tt) := {rr} <<| pendingOrders(tt)
        ELSE pendingOrders(tt)(rr) := pendingOrders(tt)(rr) - am 
        END        
    END;
    
//    4 - Análise 
    
    me <-- getMenuRecipeExpectation(rr) =
    PRE rr: menu
    THEN me:= expectedMenu(rr)
    END;
    
    me <-- getMenuRecipeCompletion(rr) =
    PRE rr: menu
    THEN me:= completedOrders(rr)
    END;

//    5 - Deletar dados
    
    beginNewDay =
    PRE !tt.(tt : tables => dom(pendingOrders(tt)) = {})
    THEN completedOrders := menu * {0}
    END

END

library(readxl)
library(neuralnet)
library(hydroGOF)
library(leaps)



normaliza_tarefa <- function(e) {
  e$Tarefa[e$Tarefa == "Work"] <- 1
  e$Tarefa[e$Tarefa == "programming"] <- 2
  e$Tarefa[e$Tarefa == "office"] <- 3
  e$Tarefa <- as.numeric(e$Tarefa)
  e$Tarefa[e$Tarefa == 1] <- round(1/3, digits = 2)
  e$Tarefa[e$Tarefa == 2] <- round(2/3, digits = 2)
  e$Tarefa[e$Tarefa == 3] <- round(3/3, digits = 2)
  return(e)
}



normaliza_exaustao <- function(e) {
  e$Exaustao[e$Exaustao == 1] <- round(1/3, digits = 2)
  e$Exaustao[e$Exaustao == 2] <- round(1/3, digits = 2)
  e$Exaustao[e$Exaustao == 3] <- round(2/3, digits = 2)
  e$Exaustao[e$Exaustao == 4] <- round(2/3, digits = 2)
  e$Exaustao[e$Exaustao == 5] <- round(3/3, digits = 2)
  e$Exaustao[e$Exaustao == 6] <- round(3/3, digits = 2)
  e$Exaustao[e$Exaustao == 7] <- round(3/3, digits = 2)
  return(e)
}



normaliza_colunas <- function(e) {
  e[,1:8] <- (e[,1:8] + 1) / 2
  return(e)
}



shuffle <- function(e) {
  e <- e[sample.int(nrow(e)), ]
  return(e)
}



abrir_xls <- function(path) {
  e <- read_excel(path, skip = 1)
  return(e)
}



test_optimal <- function(e = "geral") {
  if (e == "treino")
    regg1 <- regsubsets(Exaustao ~ KDT + MA + MV + TBC + DDC + DMS + AED + ADMSL, package$treino, nvmax = 10)
  else
    regg1 <- regsubsets(Exaustao ~ KDT + MA + MV + TBC + DDC + DMS + AED + ADMSL, package$exaustao, nvmax = 10)
  print(summary(regg1))
}



init_pacote <- function(tt = 1:500, tst = 501:844, path = "C:/Users/joaor/Desktop/SRCR/dados/exaustao.xlsx") {
  e <- abrir_xls(path)
  e <- normaliza_tarefa(e)
  e <- normaliza_exaustao(e)
  
  #Aumenta-se o erro quando se normaliza entre 0 e 1
  #e <- normaliza_colunas(e)
  
  e <- shuffle(e)
  e <- shuffle(e)
  
  pckt = NULL
  pckt$exaustao <- e
  pckt$treino   <- e[tt, ]
  pckt$teste    <- e[tst, ]
  
  return(pckt)
}



treina_rede <- function(ninter = c(7,5), alg = "rprop+") {
  p <- package
  p$nnet <- neuralnet(formula, package$treino, hidden = ninter, rep = 3, lifesign = "full", stepmax = 20000, linear.output = FALSE, threshold = 0.01, algorithm = alg)
  return(p)
}



showCasosTeste <- function() {
  p = package
  p$nnet_result <- compute(package$nnet, teste.01)
  p$result <- data.frame(atual = package$teste$Exaustao, previsao = p$nnet_result$net.result)
  
  temp <- scale(p$result$previsao)
  temp <- round(temp * 2) + 1
  
  print("RMSE:")
  print(rmse(round(p$result$atual * 3), temp))
  plot(round(p$result$atual * 3), temp, xlab = "Valor Correto", ylab = "Valor Previsto",
       col = "red", main = "Escala de Exaustao", pch = 16, cex = 1.2)
  abline(h = 1:7, v = 1:7, col = "lightgray", lty = 3)
  abline(a = 0, b = 1, lwd=2, col = "blue")
  points(round(p$result$atual * 3), temp, col = "red", pch = 16, cex = 1.2)
  return(p)
}



scale <- function(x) {
  (x - min(x)) / (max(x)-min(x))
}






#########################################################################################
#####################   IDENTIFICAR ESCALA DE NÍVEIS DE EXAUSTÃO   ######################
#########################################################################################
#####################   1 - NÃO APRESENTA SINAIS DE EXAUSTÃO       ######################
#####################   2 - APRESENTA ALGUNS SINAIS DE EXAUSTÃO    ######################
#####################   3 - APRESENTA MUITOS SINAIS DE EXAUSTÃO    ######################
#########################################################################################


#Iniciar pacote com todos os dados, incluindo teste e treino
package <- init_pacote(1:600, 601:844, "C:/Users/joaor/Desktop/SRCR/dados/exaustao.xlsx")
#Testar variaveis ótimas para os dados presentes nos casos de treino
test_optimal("treino")
#Testar variaveis ótimas para todos os dados existentes
test_optimal("geral")

#Atualizar com as variáveis desejadas
formula <- Exaustao ~  MA + MV + DMS
teste.01 <- subset(package$teste, select = c("MA","MV","DMS"))

#Treinar rede com NosInteriores e Algoritmo
package <- treina_rede(c(7,5), "rprop+")
#Testar casos de teste na rede treinada, verificar o erro e apresentar grafico de resultados
package <- showCasosTeste()


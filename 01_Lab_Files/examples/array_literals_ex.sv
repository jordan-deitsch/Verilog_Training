module a;
int k[1:3][1:4] = {{1,2,3,4},{5,6,7,8},{9,10,11,12}};
int n[1:2][1:3] = {{0,1,2},{3{4}}};
int m[1:3][1:2] = {{9,8},{2{5}},{2{6}}};
char a [1:12] = {{"H"},{"e"},{"l"},{"l"},{"o"},{" "},{"W"},{"o"},{"r"},{"l"},{"d"},{"\n"}};
char aa [1:12] = {"H","e","l","l","o"," ","W","o","r","l","d","\n"};
bit [3:0] b [2:0][3:0] = {{1,2,3,4},{5,6,7,8},{9,10,11,12}};


initial 
begin
  $display("k:");
  for(int i = 1; i<4; i++)
    for(int j = 1; j<5; j++)
     $display(k[i][j]);

  $display("n:");
  for(int i = 1; i<3; i++)
    for(int j = 1; j<4; j++)
     $display(n[i][j]);
     
  $display("m:");
  for(int i = 1; i<4; i++)
    for(int j = 1; j<3; j++)
     $display(m[i][j]);

  $display("a:"); $write("\t");
  for(int i=1; i<13;i++)
     $write("%s",a[i]);     

  $display("aa:"); $write("\t");
  for(int i=1; i<13;i++)
     $write("%s",aa[i]);     

  $display("b:");
  for(int i = 0; i<3; i++)
    for(int j = 0; j<4; j++)
     $display(b[i][j]);

  $display("k1:");
  for(int i = 1; i<4; i++)
    for(int j = 1; j<5; j++)
     $display(k1[i][j]);

end


endmodule



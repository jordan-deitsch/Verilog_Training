library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;

entity my_design is 
  port (clk : in  std_logic;
        b   : in  std_logic_vector(2 downto 0);
        c   : out std_logic);
end entity my_design;

architecture binding of my_design is

  signal d : std_logic_vector(2 downto 0) := "000";

begin
  process (clk)
    begin
      if (clk'event and clk = '1') then
        d <= b;
      end if;
  end process;

end architecture binding;

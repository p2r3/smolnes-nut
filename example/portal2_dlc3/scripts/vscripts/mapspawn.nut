if (!("Entities" in this)) return;
IncludeScript("ppmod");
IncludeScript("savelock");

IncludeScript("smolnes");

// Converts a BGR565 pixel to an RGB888 string
function getColorString (pixel) {

  local b5 = (pixel >> 11) & 0x1F;  // 5 bits (high)
  local g6 = (pixel >> 5) & 0x3F;   // 6 bits (middle)
  local r5 = pixel & 0x1F;          // 5 bits (low)

  // Expand to 8-bit range
  local r8 = (r5 << 3) | (r5 >> 2); // 5-bit to 8-bit
  local g8 = (g6 << 2) | (g6 >> 4); // 6-bit to 8-bit
  local b8 = (b5 << 3) | (b5 >> 2); // 5-bit to 8-bit

  // Return as color string
  return r8 + " " + g8 + " " + b8;

}

ppmod.onauto(async(function () {

  // Load ROM of LJ65 as an example
  // The format is a Squirrel array of all ROM bytes
  IncludeScript("lj65_rom");
  ::smolnes_init(lj65_rom);

  // How many pixels to skip on each axis
  // Increase this to improve performance at the cost of quality
  ::pixel_skip <- 7;

  // On every frame, call each pixel's update function
  ::smolnes_render <- function () {
    EntFire("nes_pixel", "RunScriptCode", "_updatePixel()");
  };

  // Set up controller buttons
  local buttons = [ "A", "B", "Select", "Start", "Up", "Down", "Left", "Right" ];
  for (local i = 0; i < 8; i ++) {
    yield ppmod.button("prop_button", Vector(7712 - i * 32, -5168), Vector(0, 90));
    local button = yielded;
    button.GetProp().targetname = buttons[i];
    button.OnPressed(function ():(i) {
      ::key_state[i] = 1;
      ppmod.wait("::key_state["+ i +"] = 0", 1.0);
    });
    SendToConsole("ent_messages " + button.GetProp().entindex());
  }
  SendToConsole("developer 1");
  SendToConsole("con_drawnotify 0");

  if (GetMapName() == "sp_a2_triple_laser") {
    GetPlayer().SetOrigin(Vector(7600, -5136.1, 0.1));
    GetPlayer().SetAngles(16, -90, 0);
  }

  // Puts the screen next to the entrance in Triple Laser
  local origin = Vector(7472, -5440, 0);

  for (local y = 0; y < 240; y += pixel_skip) {
    for (local x = 0; x < 256; x += pixel_skip) {

      // This is a "broken" model, rendering as a 1x1 pixel self-illuminated
      // white cube on most systems. Depending on HDR/autoexposure settings,
      // you might have to turn on `mat_fullbright` to see the right colors.
      yield ppmod.create("br_camera/br_player_view_ride.mdl");
      local pixel = yielded;

      pixel.targetname = "nes_pixel";
      pixel.SetOrigin(origin + Vector(256 - x, y));
      pixel.SetAngles(0, 0, 0);
      pixel.modelScale = pixel_skip;

      // Disable all types of collision with the "pixels"
      pixel.collisionGroup = 1;
      pixel.solid = 0;
      pixel.moveType = 8;

      // Assign an `_updatePixel` function to each pixel's script scope.
      // This lets us update each pixel independently, to avoid risking
      // an SQQuerySuspend timeout.
      local scope = pixel.GetScriptScope();
      scope._updatePixel <- function ():(x, y) {
        self.Color(getColorString(frame_buffer[y * 256 + x]));
      };

    }
  }

  // Once the screen has been created, we can start the emulator
  // Change this to your desired cycle count
  ppmod.interval(function () {
    for (local _i = 0; _i < 512; _i ++) {
      EntFire("worldspawn", "CallScriptFunction", "smolnes_loop");
    }
  });

}));

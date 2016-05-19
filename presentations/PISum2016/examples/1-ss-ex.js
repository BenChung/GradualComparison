if (typeof $$cts$$runtime === "undefined") {
    if (typeof require !== "undefined") require("./cts-runtime.js");
    else if (typeof document !== "undefined") { document.writeLine("<script src=\"cts-runtime.js\"></script>"); }
    else throw new Error("Could not load ConcreteTypeScript runtime!");
}
var Gun = (function () {
    function Gun() {
    }
    $$cts$$runtime.cement(Gun.prototype,"shoot",function () {
        $$cts$$runtime.cast(Gun,this);
        return this.$$cts$$value$shoot.apply(this, arguments);
    });
    $$cts$$runtime.cement(Gun.prototype,"$$cts$$value$shoot",function () {
        console.log("bang");
    });
    return Gun;
})();
$$cts$$runtime.cementGlobal("Gun",Gun);
var Pencil = (function () {
    function Pencil() {
    }
    return Pencil;
})();
$$cts$$runtime.cementGlobal("Pencil",Pencil);
var Cowboy = (function () {
    function Cowboy() {
    }
    $$cts$$runtime.cement(Cowboy.prototype,"draw",function (gun) {
        $$cts$$runtime.cast(Cowboy,this);
        $$cts$$runtime.cast(Gun,gun);
        return this.$$cts$$value$draw.apply(this, arguments);
    });
    $$cts$$runtime.cement(Cowboy.prototype,"$$cts$$value$draw",function (gun) {
        gun.$$cts$$value$shoot();
    });
    return Cowboy;
})();
$$cts$$runtime.cementGlobal("Cowboy",Cowboy);
new Cowboy().$$cts$$value$draw(($$cts$$runtime.cast(Gun,(new Pencil()))));
